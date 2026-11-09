import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalBorel
import SMSFormula.RationalCliffordGeneralSpinLatticeHorizontalFiber
import SMSFormula.RationalIdeleClassHaarMeasure

/-!
# Haar measure on the actual horizontal general-Spin fibers

The continuous idele-class orbit map is measurable for the genuine Borel
structure on `GSpin(Q)\GSpin(A)`.  Pushing the fixed rational idele-class
Haar measure through this map gives a measure on the actual quotient carrier,
concentrated on the exact horizontal `SO` fiber.  No measurable structure is
transported through the carrier equivalence.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The idele-class orbit map through a fixed general-Spin quotient point is
continuous. -/
theorem continuous_rationalIdeleClassOrbitMap
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Continuous (fun c : RationalIdeleClassGroup =>
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        c z) :=
  V.continuous_rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient.comp
    (continuous_id.prodMk continuous_const)

/-- The idele-class orbit map is measurable for the actual quotient Borel
structure, which has already been identified with the raw map-generated
structure. -/
theorem measurable_rationalIdeleClassOrbitMap
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measurable (fun c : RationalIdeleClassGroup =>
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        c z) :=
  (V.continuous_rationalIdeleClassOrbitMap z).measurable

/-- Haar measure on the actual horizontal torsor through `z`, regarded as a
measure on the ambient general-Spin quotient carrier. -/
noncomputable def horizontalFiberHaarMeasure
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measure V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.map
    (fun c : RationalIdeleClassGroup =>
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        c z)
    rationalIdeleClassHaarMeasure

@[simp]
theorem horizontalFiberHaarMeasure_univ
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.horizontalFiberHaarMeasure z Set.univ =
      rationalIdeleClassHaarMeasure Set.univ := by
  rw [horizontalFiberHaarMeasure,
    Measure.map_apply_of_aemeasurable
      (V.measurable_rationalIdeleClassOrbitMap z).aemeasurable
      MeasurableSet.univ]
  simp

/-- On a measurable set, the fiber Haar measure is the Haar mass of its
literal orbit preimage. -/
theorem horizontalFiberHaarMeasure_apply
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    {s : Set V.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hs : MeasurableSet s) :
    V.horizontalFiberHaarMeasure z s =
      rationalIdeleClassHaarMeasure
        ((fun c : RationalIdeleClassGroup =>
          V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
            c z) ⁻¹' s) := by
  exact Measure.map_apply_of_aemeasurable
    (V.measurable_rationalIdeleClassOrbitMap z).aemeasurable hs

/-- The pushed Haar measure vanishes on every measurable set disjoint from
the exact horizontal `SO` fiber through `z`. -/
theorem horizontalFiberHaarMeasure_apply_eq_zero_of_disjoint_fiber
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    {s : Set V.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hs : MeasurableSet s)
    (hdisj : Disjoint s
      {w | V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z}) :
    V.horizontalFiberHaarMeasure z s = 0 := by
  rw [V.horizontalFiberHaarMeasure_apply z hs]
  have hempty :
      (fun c : RationalIdeleClassGroup =>
        V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z) ⁻¹' s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro c hc
    exact Set.disjoint_left.1 hdisj hc
      (V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_scalarAction
        c z)
  rw [hempty, measure_empty]

/-- Translating the chosen origin inside its horizontal torsor does not
change the pushed Haar measure. -/
theorem horizontalFiberHaarMeasure_scalarAction
    (c : RationalIdeleClassGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.horizontalFiberHaarMeasure
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z) =
      V.horizontalFiberHaarMeasure z := by
  let orbit := fun d : RationalIdeleClassGroup =>
    V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient d z
  let leftMul := fun d : RationalIdeleClassGroup => c * d
  have hleft : Measurable leftMul := by
    simpa [leftMul] using
      ((continuous_const : Continuous
          (fun _ : RationalIdeleClassGroup => c)).mul
        (continuous_id : Continuous
          (fun d : RationalIdeleClassGroup => d))).measurable
  have horbit : Measurable orbit := V.measurable_rationalIdeleClassOrbitMap z
  rw [horizontalFiberHaarMeasure, horizontalFiberHaarMeasure]
  have hfun :
      (fun d : RationalIdeleClassGroup =>
        V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient d
          (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
            c z)) = orbit ∘ leftMul := by
    funext d
    rw [V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient_mul]
    exact congrArg (fun e =>
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient e z)
      (mul_comm d c)
  rw [hfun, ← Measure.map_map horbit hleft]
  change Measure.map orbit (Measure.map leftMul rationalIdeleClassHaarMeasure) =
    Measure.map orbit rationalIdeleClassHaarMeasure
  exact congrArg (Measure.map orbit)
    (Measure.IsMulLeftInvariant.map_mul_left_eq_self c)

/-- The horizontal fiber Haar measure depends only on the corresponding
`SO` quotient point, not on the chosen general-Spin lift. -/
theorem horizontalFiberHaarMeasure_eq_of_sameSO
    {z w : V.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hzw :
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z) :
    V.horizontalFiberHaarMeasure w = V.horizontalFiberHaarMeasure z := by
  obtain ⟨c, rfl⟩ :=
    (V.fullAdelicCliffordGeneralSpinLeftQuotient_sameSO_iff_ideleClassOrbit
      z w).1 hzw.symm
  exact V.horizontalFiberHaarMeasure_scalarAction c z

end RationalQuadraticSpaceMatrix
