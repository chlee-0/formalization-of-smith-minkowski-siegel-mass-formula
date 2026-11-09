import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRationalFiberBindPeriodization

/-!
# The complete rational shell-coset raw-fiber kernel

The complete countable sum of raw orbit fibers is invariant under right
multiplication by the complement stabilizer.  Its inverse right translates
therefore form a measurable kernel on the full-adelic shell, without a
representative or section.  Pointwise periodization of the crossed rational
fiber is exactly the vertical scalar times this kernel.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open ProbabilityTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellRawCosetSumInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellRawCosetSumFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellRawCosetSumT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellRawCosetSumSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellRawCosetSumSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellRawCosetSumSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellRawCosetSumSourcePolishSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    PolishSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupPolishSpaceForMeasurableDescent

noncomputable local instance fullAdelicShellRawCosetSumStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellRawCosetSumQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellRawCosetSumQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellRawCosetSumQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellRawCosetSumQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellRawCosetSumTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance fullAdelicShellRawCosetSumTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellRawCosetSumCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Countable
      ((W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
          W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) := by
  let V := W.nonisotropicLastExtension a ha
  letI : Countable V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  exact Function.Surjective.countable
    (f := QuotientGroup.mk) Quotient.mk_surjective

/-- The complete countable sum of literal raw orbit fibers over the rational
shell right-coset type. -/
def fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup) :=
  Measure.sum fun xi :
      (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
          W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
    W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure a ha xi

/-- Each rational shell-coset raw orbit fiber is invariant under literal
complement-stabilizer right translation. -/
theorem map_fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure_rightMul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (xi : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)
    (k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
    Measure.map
        (fun z : (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup) => z * k.1)
        (W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
          a ha xi) =
      W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
        a ha xi := by
  induction xi using Quotient.inductionOn with
  | _ gamma =>
      rw [W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure_mk]
      change Measure.map (fun z => z * k.1)
          (W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel
            a ha (gamma : (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup))) = _
      rw [W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply a ha]
      let muH :=
        W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha
      letI : Measure.IsMulRightInvariant muH :=
        W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isMulRightInvariant
          a ha
      calc
        Measure.map (fun z => z * k.1)
            (Measure.map
              (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
                a ha => (gamma : (W.nonisotropicLastExtension a ha
                  |>.FullAdelicCliffordGeneralSpinGroup)) * h.1) muH) =
          Measure.map
            (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
              a ha => (gamma : (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)) * h.1)
            (Measure.map (fun h => h * k) muH) := by
              rw [Measure.map_map (by fun_prop) (by fun_prop),
                Measure.map_map (by fun_prop) (by fun_prop)]
              congr 1
              funext h
              simp only [Function.comp_apply, Subgroup.coe_mul, mul_assoc]
        _ = Measure.map
            (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
              a ha => (gamma : (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)) * h.1) muH := by
          rw [map_mul_right_eq_self muH k]

/-- The complete rational shell-coset raw-fiber sum has the same right
invariance. -/
theorem map_fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure_rightMul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
    Measure.map
        (fun z : (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup) => z * k.1)
        (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
          W a ha) =
      fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
        W a ha := by
  rw [fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure,
    Measure.map_sum (measurable_mul_const k.1).aemeasurable]
  congr 1
  funext xi
  exact map_fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure_rightMul W a ha xi k

noncomputable local instance fullAdelicShellRawCosetSumFiberSFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (xi : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) :
    SFinite
      (W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
        a ha xi) := by
  induction xi using Quotient.inductionOn with
  | _ gamma =>
      rw [W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure_mk]
      rw [W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply a ha]
      infer_instance

noncomputable local instance fullAdelicShellRawCosetSumSFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SFinite (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure W a ha) := by
  rw [fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure]
  infer_instance

/-- The measurable ambient family of inverse right translates of the complete
raw rational shell-coset sum. -/
noncomputable def fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Kernel
      (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup)
      (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup) := by
  let V := W.nonisotropicLastExtension a ha
  let G := V.FullAdelicCliffordGeneralSpinGroup
  exact Kernel.map
    (Kernel.compProd (Kernel.id : Kernel G G)
      (Kernel.const (G × G)
        (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
          W a ha)))
    (fun p : G × G => p.2 * p.1⁻¹)

/-- At `g`, the ambient family is the literal inverse right translate of the
complete raw rational shell-coset sum. -/
theorem fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel W a ha g =
      Measure.map (fun z => z * g⁻¹)
        (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
          W a ha) := by
  let V := W.nonisotropicLastExtension a ha
  let G := V.FullAdelicCliffordGeneralSpinGroup
  have hmeas : Measurable (fun p : G × G => p.2 * p.1⁻¹) := by fun_prop
  ext s hs
  rw [fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel]
  rw [Kernel.map_apply' _ hmeas g hs]
  rw [Kernel.compProd_apply (hs.preimage hmeas)]
  change ∫⁻ b : G,
      (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure W a ha)
        (Prod.mk b ⁻¹' ((fun p : G × G => p.2 * p.1⁻¹) ⁻¹' s))
      ∂Measure.dirac g = _
  rw [lintegral_dirac]
  rw [Measure.map_apply (measurable_mul_const g⁻¹) hs]
  rfl

/-- The inverse-translated ambient family is constant on the native shell
right-coset relation. -/
theorem fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel_mul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup))
    (k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
    fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel W a ha (g * k.1) =
      fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel W a ha g := by
  rw [fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel_apply,
    fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel_apply]
  rw [mul_inv_rev]
  calc
    Measure.map (fun z => z * (k.1⁻¹ * g⁻¹))
        (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
          W a ha) =
        Measure.map (fun z => z * g⁻¹)
          (Measure.map (fun z => z * (k⁻¹).1)
            (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
              W a ha)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext z
      simp only [Function.comp_apply, Subgroup.coe_inv, mul_assoc]
    _ = Measure.map (fun z => z * g⁻¹)
        (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
          W a ha) := by
      rw [map_fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure_rightMul
        W a ha k⁻¹]

/-- The section-free inverse-translated raw coset-sum measure on the standard
native shell quotient. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha →
      Measure ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Quotient.lift
    (fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel W a ha)
    (fun g h hrel ↦ by
      change QuotientGroup.leftRel
        (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
          a ha RationalAdele) g h at hrel
      rw [QuotientGroup.leftRel_apply] at hrel
      let k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha :=
        ⟨g⁻¹ * h, hrel⟩
      have hh : h = g * k.1 := by
        change h = g * (g⁻¹ * h)
        symm
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [hh, fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel_mul W a ha g k])

/-- Evaluating the descended quotient measure at a quotient class recovers
the ambient inverse-translated kernel. -/
@[simp]
theorem fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure W a ha
        (QuotientGroup.mk g) =
      fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel W a ha g :=
  rfl

/-- The quotient raw coset-sum measure varies measurably in the native Borel
structure. -/
theorem measurable_fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measurable
      (fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure W a ha) := by
  letI : T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    fullAdelicShellRawCosetSumQuotientT2Space W a ha
  letI : SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    fullAdelicShellRawCosetSumQuotientSecondCountable W a ha
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  rw [measurable_iff_le_map]
  change Measure.instMeasurableSpace ≤
    MeasurableSpace.map
      (fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure W a ha)
      (borel X)
  have hq : MeasurableSpace.map q (borel G) = borel X :=
    continuous_quotient_mk'.map_borel_eq QuotientGroup.mk_surjective
  rw [← hq, MeasurableSpace.map_comp]
  exact
    (fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel W a ha
      |>.measurable).le_map

/-- The native-Borel raw coset-sum kernel on the standard shell quotient. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientRawCosetSumKernel
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Kernel
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha)
      ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) where
  toFun := fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure W a ha
  measurable' :=
    measurable_fullAdelicNonisotropicLastShellQuotientRawCosetSumMeasure
      W a ha

/-- The representative-free raw coset-sum kernel on the existing quadratic
shell, obtained through the certified native quotient equivalence. -/
noncomputable def fullAdelicNonisotropicLastShellRawCosetSumKernel
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Kernel
      (W.nonisotropicLastQuadraticShell a ha RationalAdele)
      ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Kernel.comap
    (fullAdelicNonisotropicLastShellQuotientRawCosetSumKernel W a ha)
    (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
    (W.measurable_fullAdelicNonisotropicLastShellQuotientEquiv_symm_forRationalFiber
      a ha)

/-- At an actual shell orbit, the raw coset-sum kernel is the literal inverse
right translate of the complete rational shell-coset sum. -/
theorem fullAdelicNonisotropicLastShellRawCosetSumKernel_orbit
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    fullAdelicNonisotropicLastShellRawCosetSumKernel W a ha
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele g) =
      Measure.map (fun z => z * g⁻¹)
        (fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure
          W a ha) := by
  rw [fullAdelicNonisotropicLastShellRawCosetSumKernel, Kernel.comap_apply]
  have hclass :
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele g) = QuotientGroup.mk g := by
    apply (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).injective
    simp
  rw [hclass]
  exact fullAdelicNonisotropicLastShellAmbientRawCosetSumKernel_apply W a ha g

/-- Pointwise rational-diagonal periodization of the crossed rational fiber is
the vertical scalar times the representative-free raw coset-sum kernel. -/
theorem periodized_nonisotropicLastShellRationalFiberKernel_eq_smul_rawCosetSumKernel
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (x : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.fullAdelicNonisotropicLastShellRationalFiberKernel
          L hn a ha hsurj x) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        fullAdelicNonisotropicLastShellRawCosetSumKernel W a ha x := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  dsimp only
  obtain ⟨g, rfl⟩ :=
    CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
      W a ha x
  rw [D.periodized_nonisotropicLastShellRationalFiberKernel_orbit
    L hn a ha hsurj g]
  rw [fullAdelicNonisotropicLastShellRawCosetSumKernel_orbit W a ha g]
  rfl

end RationalQuadraticSpaceMatrix
