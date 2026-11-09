import SMSFormula.AdelicProperFullPresentation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Canonically normalized additive measure on the rational adeles

This file fixes the additive measure scale that will underlie adelic
coordinates for rational invariant differentials.  The finite measure gives
the everywhere-integral finite adeles volume one.  The infinite measure is
Lebesgue measure transported through the canonical identification
`A_ℚ,∞ ≃ ℝ`.  Their product is the additive measure on the full adele ring.

No group Haar measure or Tamagawa number is defined here.
-/

open MeasureTheory Set TopologicalSpace

namespace PositiveDefiniteIntegralLattice

/-! ## Borel measurable structures -/

noncomputable instance rationalFiniteAdeleMeasurableSpace :
    MeasurableSpace RationalFiniteAdele :=
  borel RationalFiniteAdele

instance rationalFiniteAdeleBorelSpace :
    BorelSpace RationalFiniteAdele :=
  ⟨rfl⟩

noncomputable instance rationalInfiniteAdeleMeasurableSpace :
    MeasurableSpace RationalInfiniteAdele :=
  borel RationalInfiniteAdele

instance rationalInfiniteAdeleBorelSpace :
    BorelSpace RationalInfiniteAdele :=
  ⟨rfl⟩

noncomputable instance rationalInfiniteAdeleSecondCountableTopology :
    SecondCountableTopology RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.secondCountableTopology

noncomputable instance rationalAdeleMeasurableSpace :
    MeasurableSpace RationalAdele :=
  show MeasurableSpace (RationalInfiniteAdele × RationalFiniteAdele) from
    inferInstance

instance rationalAdeleBorelSpace :
    BorelSpace RationalAdele := by
  show BorelSpace (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable instance rationalAdeleSecondCountableTopology :
    SecondCountableTopology RationalAdele :=
  show SecondCountableTopology
      (RationalInfiniteAdele × RationalFiniteAdele) from
    inferInstance

/-! ## Finite adeles -/

/-- The everywhere-integral finite adeles, regarded as the positive compact
that fixes the finite additive Haar scale. -/
def integralFiniteAdelePositiveCompacts :
    PositiveCompacts RationalFiniteAdele where
  carrier := integralFiniteAdeleSubring
  isCompact' := isCompact_integralFiniteAdeleSubring
  interior_nonempty' := by
    rw [isOpen_integralFiniteAdeleSubring.interior_eq]
    exact ⟨0, integralFiniteAdeleSubring.zero_mem⟩

noncomputable instance rationalFiniteAdeleLocallyCompactSpace :
    LocallyCompactSpace RationalFiniteAdele :=
  integralFiniteAdelePositiveCompacts.locallyCompactSpace_of_addGroup

/-- Additive Haar measure on the finite rational adeles, normalized so the
everywhere-integral compact open has volume one. -/
noncomputable def rationalFiniteAdeleAddHaarMeasure :
    Measure RationalFiniteAdele :=
  Measure.addHaarMeasure integralFiniteAdelePositiveCompacts

@[simp]
theorem rationalFiniteAdeleAddHaarMeasure_integral :
    rationalFiniteAdeleAddHaarMeasure
      (integralFiniteAdeleSubring : Set RationalFiniteAdele) = 1 :=
  Measure.addHaarMeasure_self

noncomputable instance rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure :
    rationalFiniteAdeleAddHaarMeasure.IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure
    integralFiniteAdelePositiveCompacts

noncomputable instance rationalFiniteAdeleAddHaarMeasure_sigmaFinite :
    SigmaFinite rationalFiniteAdeleAddHaarMeasure :=
  inferInstance

/-! ## Infinite adeles -/

/-- The canonical identification of the unique rational infinite completion
with the real additive topological group. -/
noncomputable def rationalInfiniteAdeleContinuousAddEquivReal :
    RationalInfiniteAdele ≃ₜ+ ℝ :=
  ContinuousAddEquiv.mk rationalInfiniteAdeleRingEquivReal.toAddEquiv
    rationalInfiniteAdeleHomeomorphReal.continuous
    rationalInfiniteAdeleHomeomorphReal.symm.continuous

@[simp]
theorem rationalInfiniteAdeleContinuousAddEquivReal_apply
    (x : RationalInfiniteAdele) :
    rationalInfiniteAdeleContinuousAddEquivReal x =
      rationalInfiniteAdeleRingEquivReal x :=
  rfl

/-- Lebesgue measure transported to the rational infinite adeles. -/
noncomputable def rationalInfiniteAdeleAddHaarMeasure :
    Measure RationalInfiniteAdele :=
  Measure.map rationalInfiniteAdeleContinuousAddEquivReal.symm
    (volume : Measure ℝ)

noncomputable instance rationalInfiniteAdeleAddHaarMeasure_isAddHaarMeasure :
    rationalInfiniteAdeleAddHaarMeasure.IsAddHaarMeasure := by
  dsimp [rationalInfiniteAdeleAddHaarMeasure]
  infer_instance

noncomputable instance rationalInfiniteAdeleAddHaarMeasure_sigmaFinite :
    SigmaFinite rationalInfiniteAdeleAddHaarMeasure := by
  dsimp [rationalInfiniteAdeleAddHaarMeasure]
  exact
    rationalInfiniteAdeleContinuousAddEquivReal.symm.toMeasurableEquiv.sigmaFinite_map

theorem rationalInfiniteAdeleAddHaarMeasure_map_eq_volume :
    Measure.map rationalInfiniteAdeleContinuousAddEquivReal
      rationalInfiniteAdeleAddHaarMeasure = (volume : Measure ℝ) := by
  ext s hs
  calc
    Measure.map rationalInfiniteAdeleContinuousAddEquivReal
        rationalInfiniteAdeleAddHaarMeasure s =
        rationalInfiniteAdeleAddHaarMeasure
          (rationalInfiniteAdeleContinuousAddEquivReal ⁻¹' s) :=
      Measure.map_apply_of_aemeasurable
        rationalInfiniteAdeleContinuousAddEquivReal.measurable.aemeasurable hs
    _ = volume
        (rationalInfiniteAdeleContinuousAddEquivReal.symm ⁻¹'
          (rationalInfiniteAdeleContinuousAddEquivReal ⁻¹' s)) := by
      rw [rationalInfiniteAdeleAddHaarMeasure]
      exact Measure.map_apply_of_aemeasurable
        rationalInfiniteAdeleContinuousAddEquivReal.symm.measurable.aemeasurable
        (hs.preimage rationalInfiniteAdeleContinuousAddEquivReal.measurable)
    _ = volume s := by
      congr 1
      ext x
      simp

/-- The pullback of the standard real unit interval to the infinite adele
factor. -/
def rationalInfiniteAdeleUnitInterval :
    Set RationalInfiniteAdele :=
  rationalInfiniteAdeleContinuousAddEquivReal ⁻¹' Icc (0 : ℝ) 1

theorem measurableSet_rationalInfiniteAdeleUnitInterval :
    MeasurableSet rationalInfiniteAdeleUnitInterval :=
  measurableSet_Icc.preimage
    rationalInfiniteAdeleContinuousAddEquivReal.measurable

theorem isCompact_rationalInfiniteAdeleUnitInterval :
    IsCompact rationalInfiniteAdeleUnitInterval :=
  rationalInfiniteAdeleContinuousAddEquivReal.toHomeomorph.isCompact_preimage.mpr
    isCompact_Icc

@[simp]
theorem rationalInfiniteAdeleAddHaarMeasure_unitInterval :
    rationalInfiniteAdeleAddHaarMeasure
      rationalInfiniteAdeleUnitInterval = 1 := by
  rw [rationalInfiniteAdeleAddHaarMeasure]
  calc
    Measure.map rationalInfiniteAdeleContinuousAddEquivReal.symm volume
        rationalInfiniteAdeleUnitInterval =
        volume
          (rationalInfiniteAdeleContinuousAddEquivReal.symm ⁻¹'
            rationalInfiniteAdeleUnitInterval) :=
      Measure.map_apply_of_aemeasurable
        rationalInfiniteAdeleContinuousAddEquivReal.symm.measurable.aemeasurable
        measurableSet_rationalInfiniteAdeleUnitInterval
    _ = 1 := by
      have hpre :
          rationalInfiniteAdeleContinuousAddEquivReal.symm ⁻¹'
            rationalInfiniteAdeleUnitInterval = Icc (0 : ℝ) 1 := by
        ext x
        simp [rationalInfiniteAdeleUnitInterval]
      rw [hpre, Real.volume_Icc]
      norm_num

/-! ## Full adeles -/

/-- The real unit interval transported to the rational infinite completion,
as a positive compact. -/
noncomputable def rationalInfiniteAdeleUnitIntervalPositiveCompacts :
    PositiveCompacts RationalInfiniteAdele :=
  PositiveCompacts.Icc01.map
    rationalInfiniteAdeleContinuousAddEquivReal.symm
    rationalInfiniteAdeleContinuousAddEquivReal.symm.continuous
    rationalInfiniteAdeleContinuousAddEquivReal.symm.toHomeomorph.isOpenMap

@[simp]
theorem coe_rationalInfiniteAdeleUnitIntervalPositiveCompacts :
    (rationalInfiniteAdeleUnitIntervalPositiveCompacts :
      Set RationalInfiniteAdele) = rationalInfiniteAdeleUnitInterval := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [rationalInfiniteAdeleUnitInterval] using hy
  · intro hx
    refine
      ⟨rationalInfiniteAdeleContinuousAddEquivReal x, ?_, ?_⟩
    · simpa [rationalInfiniteAdeleUnitInterval] using hx
    · change rationalInfiniteAdeleContinuousAddEquivReal.symm
        (rationalInfiniteAdeleContinuousAddEquivReal x) = x
      exact rationalInfiniteAdeleContinuousAddEquivReal.symm_apply_apply x

/-- The standard positive compact in the full rational adeles: the real unit
interval times the integral finite adeles. -/
noncomputable def rationalAdeleStandardPositiveCompacts :
    PositiveCompacts RationalAdele :=
  show PositiveCompacts (RationalInfiniteAdele × RationalFiniteAdele) from
    rationalInfiniteAdeleUnitIntervalPositiveCompacts ×ˢ
      integralFiniteAdelePositiveCompacts

noncomputable instance rationalAdeleLocallyCompactSpace :
    LocallyCompactSpace RationalAdele :=
  rationalAdeleStandardPositiveCompacts.locallyCompactSpace_of_addGroup

/-- Additive Haar measure on the full rational adeles, fixed directly by the
standard adelic positive compact. -/
noncomputable def rationalAdeleAddHaarMeasure :
    Measure RationalAdele :=
  Measure.addHaarMeasure rationalAdeleStandardPositiveCompacts

noncomputable instance rationalAdeleAddHaarMeasure_isAddHaarMeasure :
    rationalAdeleAddHaarMeasure.IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure
    rationalAdeleStandardPositiveCompacts

noncomputable instance rationalAdeleAddHaarMeasure_sigmaFinite :
    SigmaFinite rationalAdeleAddHaarMeasure :=
  inferInstance

/-- A standard additive fundamental block: the real unit interval times the
integral finite adeles. -/
noncomputable def rationalAdeleStandardBlock : Set RationalAdele :=
  rationalAdeleStandardPositiveCompacts

@[simp]
theorem rationalAdeleStandardBlock_eq :
    rationalAdeleStandardBlock =
      rationalInfiniteAdeleUnitInterval ×ˢ
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  change
    ((rationalInfiniteAdeleUnitIntervalPositiveCompacts ×ˢ
      integralFiniteAdelePositiveCompacts :
        PositiveCompacts
          (RationalInfiniteAdele × RationalFiniteAdele)) : Set _) =
      rationalInfiniteAdeleUnitInterval ×ˢ
        (integralFiniteAdeleSubring : Set RationalFiniteAdele)
  rw [PositiveCompacts.coe_prod,
    coe_rationalInfiniteAdeleUnitIntervalPositiveCompacts]
  rfl

theorem measurableSet_rationalAdeleStandardBlock :
    MeasurableSet rationalAdeleStandardBlock :=
  rationalAdeleStandardBlock_eq ▸
    measurableSet_rationalInfiniteAdeleUnitInterval.prod
      isOpen_integralFiniteAdeleSubring.measurableSet

theorem isCompact_rationalAdeleStandardBlock :
    IsCompact rationalAdeleStandardBlock :=
  rationalAdeleStandardPositiveCompacts.isCompact

@[simp]
theorem rationalAdeleAddHaarMeasure_standardBlock :
    rationalAdeleAddHaarMeasure rationalAdeleStandardBlock = 1 := by
  exact Measure.addHaarMeasure_self

set_option backward.isDefEq.respectTransparency false in
/-- The directly normalized measure on the full rational adeles is literally
the product of the fixed Lebesgue measure at infinity and the finite Haar
measure for which the everywhere-integral adeles have volume one. -/
theorem rationalAdeleAddHaarMeasure_eq_prod :
    rationalAdeleAddHaarMeasure =
      rationalInfiniteAdeleAddHaarMeasure.prod
        rationalFiniteAdeleAddHaarMeasure := by
  letI : SigmaFinite
      (rationalInfiniteAdeleAddHaarMeasure.prod
        rationalFiniteAdeleAddHaarMeasure) :=
    Measure.prod.instSigmaFinite
  letI : (rationalInfiniteAdeleAddHaarMeasure.prod
      rationalFiniteAdeleAddHaarMeasure).IsAddLeftInvariant :=
    Measure.prod.instIsAddLeftInvariant
  apply (Measure.addHaarMeasure_eq_iff
    rationalAdeleStandardPositiveCompacts _).2
  change (rationalInfiniteAdeleAddHaarMeasure.prod
      rationalFiniteAdeleAddHaarMeasure) rationalAdeleStandardBlock = 1
  rw [rationalAdeleStandardBlock_eq, Measure.prod_prod,
    rationalInfiniteAdeleAddHaarMeasure_unitInterval,
    rationalFiniteAdeleAddHaarMeasure_integral, one_mul]

theorem rationalAdeleAddHaarMeasure_ne_zero :
    rationalAdeleAddHaarMeasure ≠ 0 := by
  intro hzero
  have h : (1 : ENNReal) = 0 := calc
    1 = rationalAdeleAddHaarMeasure rationalAdeleStandardBlock :=
      rationalAdeleAddHaarMeasure_standardBlock.symm
    _ = 0 := by rw [hzero]; rfl
  exact one_ne_zero h

/-! ## Finite adelic coordinate spaces -/

/-- The product of the standard adelic block in every coordinate. -/
noncomputable def rationalAdeleCoordinateStandardBlock (d : ℕ) :
    Set (Fin d → RationalAdele) :=
  Set.univ.pi fun _ => rationalAdeleStandardBlock

noncomputable instance rationalAdeleCoordinateMeasurableSpace (d : ℕ) :
    MeasurableSpace (Fin d → RationalAdele) :=
  MeasurableSpace.pi

instance rationalAdeleCoordinateBorelSpace (d : ℕ) :
    BorelSpace (Fin d → RationalAdele) :=
  Pi.borelSpace

/-- The coordinate parallelotope attached to the standard adelic block,
regarded as a positive compact. -/
noncomputable def rationalAdeleCoordinatePositiveCompacts (d : ℕ) :
    PositiveCompacts (Fin d → RationalAdele) where
  carrier := rationalAdeleCoordinateStandardBlock d
  isCompact' := by
    have heq :
        rationalAdeleCoordinateStandardBlock d =
          {x : Fin d → RationalAdele |
            ∀ i, x i ∈ rationalAdeleStandardBlock} := by
      ext x
      simp [rationalAdeleCoordinateStandardBlock]
    rw [heq]
    exact isCompact_pi_infinite
      (fun _ : Fin d => isCompact_rationalAdeleStandardBlock)
  interior_nonempty' := by
    rw [rationalAdeleCoordinateStandardBlock,
      interior_pi_set Set.finite_univ]
    let x : Fin d → RationalAdele :=
      fun _ => Classical.choose
        rationalAdeleStandardPositiveCompacts.interior_nonempty
    refine ⟨x, ?_⟩
    intro i _
    exact Classical.choose_spec
      rationalAdeleStandardPositiveCompacts.interior_nonempty

noncomputable instance rationalAdeleCoordinateLocallyCompactSpace (d : ℕ) :
    LocallyCompactSpace (Fin d → RationalAdele) :=
  (rationalAdeleCoordinatePositiveCompacts d).locallyCompactSpace_of_addGroup

/-- Additive Haar measure on a finite adelic coordinate space, normalized
directly so the standard coordinate parallelotope has volume one. -/
noncomputable def rationalAdeleCoordinateAddHaarMeasure (d : ℕ) :
    Measure (Fin d → RationalAdele) :=
  Measure.addHaarMeasure (rationalAdeleCoordinatePositiveCompacts d)

noncomputable instance rationalAdeleCoordinateAddHaarMeasure_isAddHaarMeasure
    (d : ℕ) :
    (rationalAdeleCoordinateAddHaarMeasure d).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure
    (rationalAdeleCoordinatePositiveCompacts d)

noncomputable instance rationalAdeleCoordinateAddHaarMeasure_sigmaFinite
    (d : ℕ) :
    SigmaFinite (rationalAdeleCoordinateAddHaarMeasure d) :=
  inferInstance

@[simp]
theorem rationalAdeleCoordinateAddHaarMeasure_standardBlock (d : ℕ) :
    rationalAdeleCoordinateAddHaarMeasure d
      (rationalAdeleCoordinateStandardBlock d) = 1 := by
  change Measure.addHaarMeasure (rationalAdeleCoordinatePositiveCompacts d)
      (rationalAdeleCoordinatePositiveCompacts d : Set
        (Fin d → RationalAdele)) = 1
  exact Measure.addHaarMeasure_self

@[simp]
theorem rationalAdeleCoordinateAddHaarMeasure_smul_standardBlock
    (d : ℕ) (c : ENNReal) :
    (c • rationalAdeleCoordinateAddHaarMeasure d)
      (rationalAdeleCoordinateStandardBlock d) = c := by
  rw [Measure.smul_apply, smul_eq_mul,
    rationalAdeleCoordinateAddHaarMeasure_standardBlock, mul_one]

/-- The standard coordinate parallelotope excludes every nontrivial common
rescaling of the canonical coordinate measure. -/
theorem rationalAdeleCoordinateAddHaarMeasure_smul_normalized_iff
    (d : ℕ) (c : ENNReal) :
    (c • rationalAdeleCoordinateAddHaarMeasure d)
        (rationalAdeleCoordinateStandardBlock d) = 1 ↔ c = 1 := by
  rw [rationalAdeleCoordinateAddHaarMeasure_smul_standardBlock]

/-- The full-adelic coordinate measure in the dimension of the rational
skew-adjoint tangent model. -/
noncomputable def rationalSkewAdjointAdeleCoordinateMeasure (n : ℕ) :
    Measure (Fin (n.choose 2) → RationalAdele) :=
  rationalAdeleCoordinateAddHaarMeasure (n.choose 2)

@[simp]
theorem rationalSkewAdjointAdeleCoordinateMeasure_standardBlock (n : ℕ) :
    rationalSkewAdjointAdeleCoordinateMeasure n
      (rationalAdeleCoordinateStandardBlock (n.choose 2)) = 1 :=
  rationalAdeleCoordinateAddHaarMeasure_standardBlock (n.choose 2)

theorem rationalSkewAdjointAdeleCoordinateMeasure_smul_normalized_iff
    (n : ℕ) (c : ENNReal) :
    (c • rationalSkewAdjointAdeleCoordinateMeasure n)
        (rationalAdeleCoordinateStandardBlock (n.choose 2)) = 1 ↔
      c = 1 :=
  rationalAdeleCoordinateAddHaarMeasure_smul_normalized_iff
    (n.choose 2) c

end PositiveDefiniteIntegralLattice
