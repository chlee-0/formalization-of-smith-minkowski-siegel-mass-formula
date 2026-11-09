import SMSFormula.AdelicGaussianFiberOrbitalComparison
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRegular
import SMSFormula.RationalQuadraticIsometryGeneralSpinFullAdelicShellMeasureTransport
import SMSFormula.RationalCliffordGeneralSpinLatticeFullAdelicSOSurjectivity

/-!
# Native orbital comparison on a supplied complement presentation

The native ambient shell is the same quadratic fiber. Its
horizontal transport scalar is kept. The supplied presentation is an input;
no rational representative or complement is chosen.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
open scoped ENNReal

local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

-- The native modules use `borel X`, while the analytic modules use the
-- equal subtype measurable structure. Prove transport abstractly so instance
-- elaboration never confuses those two presentations of the same structure.
private theorem map_id_spaceEq_apply {X : Type*} {m m' : MeasurableSpace X}
    (h : m = m') (μ : @Measure X m) (s : Set X) :
    (@Measure.map X X m m' id μ) s = μ s := by
  cases h
  simp only [Measure.map_id]

private theorem regular_map_id_spaceEq {X : Type*} [t : TopologicalSpace X]
    {m m' : MeasurableSpace X} (h : m = m') (μ : @Measure X m)
    (hμ : @Measure.Regular X m t μ) :
    @Measure.Regular X m' t (@Measure.map X X m m' id μ) := by
  cases h
  simpa only [Measure.map_id] using hμ

private theorem map_id_spaceEq_ne_zero {X : Type*} {m m' : MeasurableSpace X}
    (h : m = m') (μ : @Measure X m) (hμ : μ ≠ 0) :
    @Measure.map X X m m' id μ ≠ 0 := by
  cases h
  simpa only [Measure.map_id] using hμ

private theorem map_invariant_spaceEq {X : Type*} {m m' : MeasurableSpace X}
    (h : m = m') (μ : @Measure X m) (f : X → X)
    (hμ : @Measure.map X X m m f μ = μ) :
    @Measure.map X X m' m' f (@Measure.map X X m m' id μ) =
      @Measure.map X X m m' id μ := by
  cases h
  simpa only [Measure.map_id] using hμ

namespace RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation
variable {n m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : V.nativeRationalQuadraticForm x ≠ 0)

local instance : MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) := borel _
local instance : BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) := ⟨rfl⟩
local instance : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (V.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (V.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

/-- The existing ambient shell measure is regular; the finite inverse horizontal
scalar remains exactly the scalar in its original definition. -/
theorem anisotropicRationalAmbientShellMeasure_regular :
    (P.anisotropicRationalAmbientShellMeasure hx).Regular := by
  letI := P.lowerSpace.fullAdelicNonisotropicLastShellMeasure_regular
    (V.nativeRationalQuadraticForm x) hx
  letI := Measure.Regular.map (μ := P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
    (V.nativeRationalQuadraticForm x) hx) (P.blockToAmbientShellHomeomorph hx RationalAdele)
  apply Measure.Regular.smul
  exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr
    (ne_of_gt (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx)))

/-- Nonvanishing is forced by the coefficient-one bind to nonzero Haar. -/
theorem anisotropicRationalAmbientShellMeasure_ne_zero :
    P.anisotropicRationalAmbientShellMeasure hx ≠ 0 := by
  letI := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  intro hz
  have hbind := P.anisotropicRationalAmbientShellMeasure_bind_orbitFiberKernel_eq_horizontal hx
  rw [hz, Measure.bind_zero_left] at hbind
  exact (NeZero.ne V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) hbind.symm

include P hx in
/-- Reuse the block transitivity through the supplied shell/group maps. -/
theorem fullAdelic_anisotropicRationalAmbientShellOrbitMap_surjective :
    Function.Surjective (V.anisotropicRationalAmbientShellOrbitMap x RationalAdele) := by
  intro y
  obtain ⟨z, rfl⟩ := (P.blockToAmbientShellHomeomorph hx RationalAdele).surjective y
  obtain ⟨g, rfl⟩ := CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
    P.lowerSpace (V.nativeRationalQuadraticForm x) hx z
  exact ⟨P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g,
    (P.blockToAmbientShellHomeomorph_fullAdelic_orbit hx g).symm⟩

/-- Equivariance holds on every shell vector, not only at the basepoint. -/
theorem coe_blockToAmbientShellHomeomorph_translate
    (g : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup)
    (y : P.lowerSpace.nonisotropicLastQuadraticShell (V.nativeRationalQuadraticForm x) hx RationalAdele) :
    (P.blockToAmbientShellHomeomorph hx RationalAdele
      (P.lowerSpace.fullAdelicNonisotropicLastShellTranslate (V.nativeRationalQuadraticForm x) hx g y)).val =
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g).matrixPoint.1.mulVec
        (P.blockToAmbientShellHomeomorph hx RationalAdele y).val := by
  rw [coe_blockToAmbientShellHomeomorph, coe_fullAdelicNonisotropicLastShellTranslate,
    coe_blockToAmbientShellHomeomorph]
  exact P.blockToAmbientBaseChangeIsometryEquiv_specialOrthogonal_mulVec hx RationalAdele g.matrixPoint y.val

end RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance nativeComparisonValueFiberBorelSpace (a : RationalAdele) :
    BorelSpace (adelicValueFiber L a) := by
  unfold adelicValueFiber
  infer_instance

/-- The two shell carriers agree definitionally; no geometric identification is chosen. -/
theorem nativeAmbientShell_eq_adelicValueFiber :
    (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele : Type) =
      adelicValueFiber L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) := rfl

/-- The same native measure on the subtype Borel structure used by the analytic
fiber. This identity map only reconciles `borel subtype` with `Subtype`'s Borel
instance; the next theorem proves equality of its value on every set. -/
def nativeShellMeasureOnValueFiber :
    Measure (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))) :=
  @Measure.map _ _ (borel (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele))
    _ id (P.anisotropicRationalAmbientShellMeasure hx)

/-- The Borel interface transport changes no set mass, measurable or otherwise. -/
theorem nativeShellMeasureOnValueFiber_apply (s : Set (adelicValueFiber L
    (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) :
    nativeShellMeasureOnValueFiber L P hx s = P.anisotropicRationalAmbientShellMeasure hx s := by
  exact map_id_spaceEq_apply
    (@BorelSpace.measurable_eq _ _ _
      (nativeComparisonValueFiberBorelSpace L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).symm _ s

instance nativeShellMeasureOnValueFiber_regular :
    (nativeShellMeasureOnValueFiber L P hx).Regular := by
  exact regular_map_id_spaceEq
    (@BorelSpace.measurable_eq _ _ _
      (nativeComparisonValueFiberBorelSpace L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).symm _
    (P.anisotropicRationalAmbientShellMeasure_regular hx)

theorem nativeShellMeasureOnValueFiber_ne_zero : nativeShellMeasureOnValueFiber L P hx ≠ 0 := by
  exact map_id_spaceEq_ne_zero
    (@BorelSpace.measurable_eq _ _ _
      (nativeComparisonValueFiberBorelSpace L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).symm _
    (P.anisotropicRationalAmbientShellMeasure_ne_zero hx)

private theorem map_nativeAmbientShellMeasure_generalSpin
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    @Measure.map _ _
      (borel (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele))
      (borel (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele))
      (specialOrthogonalFiberHomeomorph L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) g.matrixGroup)
      (P.anisotropicRationalAmbientShellMeasure hx) = P.anisotropicRationalAmbientShellMeasure hx := by
  letI : MeasurableSpace (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele) := borel _
  letI : BorelSpace (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele) := ⟨rfl⟩
  letI : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
  letI : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩
  obtain ⟨g, rfl⟩ := (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).surjective g
  let e := P.blockToAmbientShellHomeomorph hx RationalAdele
  let t := P.lowerSpace.fullAdelicNonisotropicLastShellTranslate
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx g
  let A : L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele ≃ₜ
      L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x RationalAdele :=
    specialOrthogonalFiberHomeomorph L (algebraMap ℚ RationalAdele
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
    (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g).matrixGroup
  have heq : A ∘ e = e ∘ t := by
    funext y
    apply Subtype.ext
    exact (P.coe_blockToAmbientShellHomeomorph_translate hx g y).symm
  have ht : Measurable t := P.lowerSpace.measurable_fullAdelicNonisotropicLastShellTranslate
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx g
  change @Measure.map _ _ (borel _) (borel _) A
      ((P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞)⁻¹ •
        Measure.map e (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) =
    (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞)⁻¹ •
        Measure.map e (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
  rw [Measure.map_smul, Measure.map_map A.continuous.measurable e.continuous.measurable,
    heq, ← Measure.map_map e.continuous.measurable ht,
    P.lowerSpace.map_fullAdelicNonisotropicLastShellMeasure_translate]

/-- Native GSpin invariance reaches the literal analytic fiber, with the old
horizontal scalar unchanged and with no selected lift. -/
theorem map_nativeShellMeasureOnValueFiber_generalSpin
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map (specialOrthogonalFiberHomeomorph L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) g.matrixGroup)
      (nativeShellMeasureOnValueFiber L P hx) = nativeShellMeasureOnValueFiber L P hx := by
  exact map_invariant_spaceEq
    (@BorelSpace.measurable_eq _ _ _
      (nativeComparisonValueFiberBorelSpace L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).symm _ _
    (map_nativeAmbientShellMeasure_generalSpin L P hx g)

/-- The surjectivity onto SO transfers invariance; no section is chosen. -/
theorem map_nativeShellMeasureOnValueFiber_specialOrthogonal (hn : 2 ≤ n)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    Measure.map (specialOrthogonalFiberHomeomorph L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) h)
      (nativeShellMeasureOnValueFiber L P hx) = nativeShellMeasureOnValueFiber L P hx := by
  obtain ⟨r, hr⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  subst n
  obtain ⟨g, rfl⟩ := L.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective h
  exact map_nativeShellMeasureOnValueFiber_generalSpin L P hx g

include P hx in
/-- Actual transitivity at the represented nonzero rational value of the
supplied vector, reusing the old block orbit theorem and supplied presentation. -/
theorem isTransitiveAction_nativeValueFiber :
    SMSFormula.CompactOrbit.IsTransitiveAction
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))) := by
  intro y z
  obtain ⟨g, hg⟩ := P.fullAdelic_anisotropicRationalAmbientShellOrbitMap_surjective hx y
  obtain ⟨h, hh⟩ := P.fullAdelic_anisotropicRationalAmbientShellOrbitMap_surjective hx z
  let base : adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) :=
    L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShellBasepoint x RationalAdele
  let gSO : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup := g.matrixGroup
  let hSO : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup := h.matrixGroup
  have hg' : gSO • base = y := by
    apply Subtype.ext
    rw [adelicValueFiber_smul_val]
    exact congrArg Subtype.val hg
  have hh' : hSO • base = z := by
    apply Subtype.ext
    rw [adelicValueFiber_smul_val]
    exact congrArg Subtype.val hh
  exact ⟨hSO * gSO⁻¹, by rw [mul_smul, ← hg', inv_smul_smul, hh']⟩

/-- Invariance in the interface used by the existing orbital comparison. -/
theorem smulInvariantMeasure_nativeShellMeasureOnValueFiber (hn : 2 ≤ n) :
    SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
      (nativeShellMeasureOnValueFiber L P hx) := by
  constructor
  intro g s hs
  have hm := map_nativeShellMeasureOnValueFiber_specialOrthogonal L P hx hn g
  have he := Measure.map_apply (μ := nativeShellMeasureOnValueFiber L P hx)
    (specialOrthogonalFiberHomeomorph L _ g).continuous.measurable hs
  exact he.symm.trans (congrArg (fun μ ↦ μ s) hm)

/-- The original horizontal scalar is still visible in every set mass. -/
theorem nativeShellMeasureOnValueFiber_apply_horizontal
    (s : Set (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) :
    nativeShellMeasureOnValueFiber L P hx s =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞)⁻¹ *
        (@Measure.map _ _ (borel _) (borel _)
          (P.blockToAmbientShellHomeomorph hx RationalAdele)
          (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) s := by
  rw [nativeShellMeasureOnValueFiber_apply]
  rfl

/-- Core traces are integrable against the actual native measure as well. -/
theorem integrable_nativeShellMeasureOnValueFiber_core {b : ℝ} (f : realGaussianCore L b) :
    Integrable (fun y : adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) ↦ f.val y.val)
      (nativeShellMeasureOnValueFiber L P hx) :=
  (realGaussianTraceCc L b _ f).continuous.integrable_of_hasCompactSupport
    (realGaussianTraceCc L b _ f).hasCompactSupport

section Comparison
variable (hn : 4 < n) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

/-- The native denominator is strictly positive and finite, with no Riesz
nonvanishing assumption. The orbit and presentation are supplied, not chosen. -/
theorem nativeShellMeasureOnValueFiber_orbit_pos_lt_top :
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    0 < M U ∧ M U < ⊤ := by
  letI := smulInvariantMeasure_nativeShellMeasureOnValueFiber L P hx (by omega : 2 ≤ n)
  letI := secondCountableTopology_fiberActingGroup L
  letI := sigmaCompactSpace_fiberActingGroup L
  exact SMSFormula.CompactOrbit.measure_pos_lt_top_of_compactOpen_subgroup
    (nativeShellMeasureOnValueFiber L P hx)
    (isTransitiveAction_nativeValueFiber L P hx) x₀ K hc ho
    (nativeShellMeasureOnValueFiber_ne_zero L P hx)

/-- The actual Riesz measure and the existing native measure are proportional.
All comparison hypotheses are discharged at this represented nonzero rational
value; the scalar is the ratio of the two raw orbit masses, not an evaluation. -/
theorem gaussianFiberMeasure_eq_smul_nativeShellMeasure :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    σ = (σ U / M U) • M := by
  letI := smulInvariantMeasure_nativeShellMeasureOnValueFiber L P hx (by omega : 2 ≤ n)
  exact gaussianFiberMeasure_eq_smul_of_transitive L hn hb _
    (nativeShellMeasureOnValueFiber L P hx) (nativeShellMeasureOnValueFiber_ne_zero L P hx)
    (isTransitiveAction_nativeValueFiber L P hx) x₀ K hc ho

/-- Finiteness precedes any passage to `toReal`. The numerator can still be zero. -/
theorem gaussianFiberMeasure_nativeShell_ratio_lt_top :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    gaussianFiberMeasure L hn hb a U / nativeShellMeasureOnValueFiber L P hx U < ⊤ := by
  letI := smulInvariantMeasure_nativeShellMeasureOnValueFiber L P hx (by omega : 2 ≤ n)
  exact gaussianFiberMeasure_orbit_ratio_lt_top L hn hb _
    (nativeShellMeasureOnValueFiber L P hx) (nativeShellMeasureOnValueFiber_ne_zero L P hx)
    (isTransitiveAction_nativeValueFiber L P hx) x₀ K hc ho

/-- The common-shell comparison with its one unknown scalar exposed, on the
actual core and with genuine native integrability. No scalar is cancelled. -/
theorem realValueDensity_eq_nativeShell_ratio_mul_integral (f : realGaussianCore L b) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    L.rationalQuadraticSpaceMatrix.realValueDensity f.val a =
      (σ U / M U).toReal * ∫ y : adelicValueFiber L a, f.val y.val ∂M := by
  dsimp only
  rw [← integral_gaussianFiberMeasure_core L hn hb _ f]
  conv_lhs =>
    rw [gaussianFiberMeasure_eq_smul_nativeShellMeasure L P hx hn hb x₀ K hc ho,
      integral_smul_measure, smul_eq_mul]

/-- One independently proved raw orbit-mass equality suffices. This theorem
keeps that calibration as an input; invariance and regularity do not supply it. -/
theorem gaussianFiberMeasure_eq_nativeShellMeasure_of_orbit_mass_eq
    (hmass : gaussianFiberMeasure L hn hb
        (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
        ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) =
      nativeShellMeasureOnValueFiber L P hx
        ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))) :
    gaussianFiberMeasure L hn hb
        (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) =
      nativeShellMeasureOnValueFiber L P hx := by
  letI := smulInvariantMeasure_nativeShellMeasureOnValueFiber L P hx (by omega : 2 ≤ n)
  exact gaussianFiberMeasure_eq_of_orbit_mass_eq L hn hb _
    (nativeShellMeasureOnValueFiber L P hx) (nativeShellMeasureOnValueFiber_ne_zero L P hx)
    (isTransitiveAction_nativeValueFiber L P hx) x₀ K hc ho hmass

end Comparison
end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
