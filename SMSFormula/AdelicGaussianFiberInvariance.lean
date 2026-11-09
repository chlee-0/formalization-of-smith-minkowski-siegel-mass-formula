import SMSFormula.AdelicGaussianCoreAction

/-!
# Invariance of the actual Riesz fiber measure

The real core is stable under the action. Its density is unchanged because
the action preserves both coordinate Haar and the quadratic value. Regular
uniqueness on the literal fiber therefore identifies the translated measure
with the constructed one. This proves invariance, not native normalization.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory CompactlySupported

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ}

/-- The existing matrix-point value law, read on the full special orthogonal group. -/
theorem fullAdelicQuadraticFormValue_specialOrthogonal (V : RationalQuadraticSpaceMatrix n)
    (h : V.FullAdelicSpecialOrthogonalGroup) (x : Fin n → RationalAdele) :
    V.fullAdelicQuadraticFormValue (h.1.1.1.mulVec x) = V.fullAdelicQuadraticFormValue x :=
  V.fullAdelicQuadraticFormValue_specialOrthogonalMatrixPoint
    (V.specialOrthogonalMatrixPointOfGroup RationalAdele h) x

/-- Coefficient invariance at the full SO group. This uses the same Haar/value
argument as the old GSpin coefficient law, with no lift to GSpin selected. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_comp_specialOrthogonal
    (V : RationalQuadraticSpaceMatrix n) (h : V.FullAdelicSpecialOrthogonalGroup)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient (fun x ↦ Phi (h.1.1.1.mulVec x)) =
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi := by
  funext t
  have hp : MeasurePreserving (fullAdelicMatrixUnitMeasurableEquiv h.1.1)
      (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) :=
    V.measurePreserving_fullAdelicSpecialOrthogonal_mulVec h
  have hi := hp.integral_comp'
    (fun y ↦ Phi y * (V.rationalAdeleRankOneQuadraticPhase t y : ℂ))
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral,
    V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral, ← hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change Phi (h.1.1.1.mulVec x) * (V.rationalAdeleRankOneQuadraticPhase t x : ℂ) =
    Phi (h.1.1.1.mulVec x) * (V.rationalAdeleRankOneQuadraticPhase t (h.1.1.1.mulVec x) : ℂ)
  rw [rationalAdeleRankOneQuadraticPhase, rationalAdeleRankOneQuadraticPhase,
    V.fullAdelicQuadraticFormValue_specialOrthogonal]

/-- The real density is invariant at every value, without an L1 premise. -/
theorem realValueDensity_comp_specialOrthogonal (V : RationalQuadraticSpaceMatrix n)
    (h : V.FullAdelicSpecialOrthogonalGroup) (f : (Fin n → RationalAdele) → ℝ) :
    V.realValueDensity (fun x ↦ f (h.1.1.1.mulVec x)) = V.realValueDensity f := by
  unfold realValueDensity complexValueFourierDensity
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_comp_specialOrthogonal h (fun x ↦ (f x : ℂ))]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

/-- Restriction of the matrix homeomorphism to its preserved literal fiber. -/
def specialOrthogonalFiberHomeomorph (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    adelicValueFiber L a ≃ₜ adelicValueFiber L a :=
  (fullAdelicMatrixUnitHomeomorph h.1.1).subtype (fun x ↦ by
    change L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a ↔
      L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue (h.1.1.1.mulVec x) = a
    rw [L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue_specialOrthogonal])

@[simp] theorem specialOrthogonalFiberHomeomorph_val (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) (x : adelicValueFiber L a) :
    (specialOrthogonalFiberHomeomorph L a h x).val = h.1.1.1.mulVec x.val := rfl

/-- The actual Riesz fiber measure is invariant under every full-adelic special
orthogonal point, at every adelic value. Transitivity and representedness are
not needed for invariance; they enter only the later orbital comparison. -/
theorem map_gaussianFiberMeasure_specialOrthogonal (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    Measure.map (specialOrthogonalFiberHomeomorph L a h) (gaussianFiberMeasure L hn hb a) =
      gaussianFiberMeasure L hn hb a := by
  let e := specialOrthogonalFiberHomeomorph L a h
  haveI : (Measure.map e (gaussianFiberMeasure L hn hb a)).Regular := Measure.Regular.map e
  apply eq_gaussianFiberMeasure_of_core_integrals L hn hb a
  intro f
  change (∫ x, realGaussianTrace L b a f x ∂Measure.map e (gaussianFiberMeasure L hn hb a)) = _
  rw [integral_map e.continuous.aemeasurable (realGaussianTrace L b a f).continuous.aestronglyMeasurable]
  change (∫ x, f.val (e x).val ∂gaussianFiberMeasure L hn hb a) = _
  simp only [e, specialOrthogonalFiberHomeomorph_val]
  let F : realGaussianCore L b := ⟨fun x ↦ f.val (h.1.1.1.mulVec x),
    mem_realGaussianCore_comp_specialOrthogonal L b h f.property⟩
  exact (integral_gaussianFiberMeasure_core L hn hb a F).trans
    (congrFun (L.rationalQuadraticSpaceMatrix.realValueDensity_comp_specialOrthogonal h f.val) a)

/-- Measure preservation, including measurability of the actual fiber map. -/
theorem measurePreserving_gaussianFiberMeasure_specialOrthogonal
    (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    MeasurePreserving (specialOrthogonalFiberHomeomorph L a h)
      (gaussianFiberMeasure L hn hb a) (gaussianFiberMeasure L hn hb a) :=
  ⟨(specialOrthogonalFiberHomeomorph L a h).continuous.measurable,
    map_gaussianFiberMeasure_specialOrthogonal L hn hb a h⟩

/-- Invariance at the actual acting GSpin group, through its existing matrix group. -/
theorem map_gaussianFiberMeasure_generalSpin (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map (specialOrthogonalFiberHomeomorph L a g.matrixGroup)
        (gaussianFiberMeasure L hn hb a) = gaussianFiberMeasure L hn hb a :=
  map_gaussianFiberMeasure_specialOrthogonal L hn hb a g.matrixGroup

/-- The restriction really is the old GSpin matrix-point action. -/
theorem specialOrthogonalFiberHomeomorph_generalSpin_val (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) (x : adelicValueFiber L a) :
    (specialOrthogonalFiberHomeomorph L a g.matrixGroup x).val = g.matrixPoint.1.mulVec x.val := by
  rw [specialOrthogonalFiberHomeomorph_val, CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe]

/-- Invariance extends to the actual global functional on every C_c test.
No core-membership premise remains in this conclusion. -/
theorem gaussianFiberFunctional_comp_specialOrthogonal (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (f : C_c(adelicValueFiber L a, ℝ)) :
    gaussianFiberFunctional L hn hb a
        (f.comp (specialOrthogonalFiberHomeomorph L a h).toCocompactMap) =
      gaussianFiberFunctional L hn hb a f := by
  rw [← integral_gaussianFiberMeasure, ← integral_gaussianFiberMeasure]
  have hp : MeasurePreserving (specialOrthogonalFiberHomeomorph L a h).toMeasurableEquiv
      (gaussianFiberMeasure L hn hb a) (gaussianFiberMeasure L hn hb a) :=
    measurePreserving_gaussianFiberMeasure_specialOrthogonal L hn hb a h
  exact hp.integral_comp' f

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
