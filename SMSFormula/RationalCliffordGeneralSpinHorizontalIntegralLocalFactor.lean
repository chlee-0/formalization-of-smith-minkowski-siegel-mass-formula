import SMSFormula.RationalCliffordGeneralSpinPlacewiseHorizontalHaar
import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSimilitude
import SMSFormula.AdelicDoubleCosets

/-!
# Normalized horizontal integral factors for local general Spin

The placewise horizontal `GSpin` Haar measures have a fixed scale: on their
identity charts they push to the literal unit Haar measure times the fixed
special-orthogonal differential measure.  To form their finite-adelic
restricted product, the good-place compact-open factors must therefore be
normalized using that same ambient measure.

This file isolates the finite set where the rational Clifford structure
constants need not be integral, proves that the displayed integral `GSpin`
locus is a subgroup away from that set, and gives its comapped Haar measure
and normalized probability measure.  The reciprocal of the literal local
volume remains explicit.  No infinite product, adelic Haar measure, quotient
measure, or Tamagawa normalization is constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance horizontalIntegralLocalPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralLocalDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalIntegralLocalGroupMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance horizontalIntegralLocalGroupBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

/-! ## The finite horizontal denominator set -/

/-- The places where at least one rational Clifford structure constant used
by the integral local `GSpin` coordinates is nonintegral. -/
def cliffordGeneralSpinHorizontalIntegralBadPlaces :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (Filter.eventually_cofinite.mp
      V.eventually_cliffordGeneralSpinIntegralStructureAt).toFinset

/-- Outside the horizontal denominator set, all required Clifford structure
constants are integral. -/
theorem cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    V.CliffordGeneralSpinIntegralStructureAt v := by
  have hv' : v ∉
      (Filter.eventually_cofinite.mp
        V.eventually_cliffordGeneralSpinIntegralStructureAt).toFinset := hv
  simpa using hv'

/-! ## Good-place subgroup closure -/

/-- The identity intrinsic `GSpin` point has integral displayed coordinates
at every place where the rational Clifford structure is integral. -/
theorem padicCliffordGeneralSpinIsIntegral_one_of_integralStructure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1
      (1 : V.HeightOnePadicCliffordGeneralSpinGroup v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    simpa using V.cliffordGeneralSpinIntegralStructureAt_one v hv u
  · intro u
    simpa using V.cliffordGeneralSpinIntegralStructureAt_one v hv u
  · simp [padicIntegralUnitsSubgroup]
  · rw [V.mem_padicSpecialOrthogonalIntegralSubgroup_iff]
    constructor <;> intro i j <;>
      by_cases hij : i = j <;> simp [hij]

/-- Integral displayed `GSpin` coordinates are closed under multiplication
at every place where the rational Clifford multiplication table is integral.
-/
theorem padicCliffordGeneralSpinIsIntegral_mul_of_integralStructure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    {g h : V.HeightOnePadicCliffordGeneralSpinGroup v}
    (hg : V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 g)
    (hh : V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 h) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 (g * h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    rw [CliffordGeneralSpinIntrinsicPoint.mul_cliffordUnit]
    exact V.cliffordGeneralSpinIntegralStructureAt_mul v hv hg.1 hh.1 u
  · intro u
    rw [CliffordGeneralSpinIntrinsicPoint.mul_cliffordUnit, mul_inv_rev]
    exact V.cliffordGeneralSpinIntegralStructureAt_mul v hv hh.2.1 hg.2.1 u
  · rw [CliffordGeneralSpinIntrinsicPoint.mul_similitude]
    exact (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).mul_mem hg.2.2.1 hh.2.2.1
  · rw [CliffordGeneralSpinIntrinsicPoint.mul_matrixGroup]
    exact (V.padicSpecialOrthogonalIntegralSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).mul_mem hg.2.2.2 hh.2.2.2

/-- The displayed integral `GSpin` condition is closed under inversion. -/
theorem padicCliffordGeneralSpinIsIntegral_inv
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g : V.HeightOnePadicCliffordGeneralSpinGroup v}
    (hg : V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 g) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 g⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hg.2.1
  · simpa using hg.1
  · rw [CliffordGeneralSpinIntrinsicPoint.inv_similitude]
    exact (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).inv_mem hg.2.2.1
  · rw [CliffordGeneralSpinIntrinsicPoint.inv_matrixGroup]
    exact (V.padicSpecialOrthogonalIntegralSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).inv_mem hg.2.2.2

/-- A good finite place after adjoining an arbitrary finite exceptional set.
-/
abbrev CliffordGeneralSpinHorizontalIntegralPlace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  {v : IsDedekindDomain.HeightOneSpectrum ℤ //
    v ∉ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}

/-- The compact-open integral subgroup at a horizontal good place. -/
def padicCliffordGeneralSpinHorizontalIntegralSubgroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Subgroup (V.HeightOnePadicCliffordGeneralSpinGroup v.1) where
  carrier := {g |
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 g}
  one_mem' := by
    apply V.padicCliffordGeneralSpinIsIntegral_one_of_integralStructure v.1
    exact V.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
      v.1 (fun hv => v.2 (Finset.mem_union_right S hv))
  mul_mem' := by
    intro g h hg hh
    apply V.padicCliffordGeneralSpinIsIntegral_mul_of_integralStructure v.1
    · exact V.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
        v.1 (fun hv => v.2 (Finset.mem_union_right S hv))
    · exact hg
    · exact hh
  inv_mem' := by
    intro g hg
    exact V.padicCliffordGeneralSpinIsIntegral_inv v.1 hg

@[simp]
theorem mem_padicCliffordGeneralSpinHorizontalIntegralSubgroup_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (g : V.HeightOnePadicCliffordGeneralSpinGroup v.1) :
    g ∈ V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v ↔
      V.PadicCliffordGeneralSpinIsIntegral
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 g :=
  Iff.rfl

theorem isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    IsOpen (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v :
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1)) :=
  V.isOpen_padicCliffordGeneralSpinIsIntegral
    (Rat.HeightOneSpectrum.primesEquiv v.1).1

theorem isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    IsCompact (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v :
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1)) :=
  V.isCompact_padicCliffordGeneralSpinIsIntegral
    (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-! ## Literal horizontal volume and normalized local measure -/

/-- The good integral locus measured in the already fixed horizontal local
`GSpin` Haar scale. -/
def padicCliffordGeneralSpinHorizontalIntegralVolume
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0∞ :=
  V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
    {g | V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 g}

theorem padicCliffordGeneralSpinHorizontalIntegralVolume_lt_top
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v < ⊤ := by
  let μ := V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : Measure.IsHaarMeasure μ :=
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
  exact (V.isCompact_padicCliffordGeneralSpinIsIntegral
    (Rat.HeightOneSpectrum.primesEquiv v).1).measure_lt_top

theorem padicCliffordGeneralSpinHorizontalIntegralVolume_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    0 < V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 := by
  let μ := V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI : Measure.IsHaarMeasure μ :=
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  exact (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
    |>.measure_pos μ ⟨1, Subgroup.one_mem _⟩

theorem padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 ≠ 0 :=
  ne_of_gt (V.padicCliffordGeneralSpinHorizontalIntegralVolume_pos S v)

theorem padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v ≠ ⊤ :=
  ne_of_lt (V.padicCliffordGeneralSpinHorizontalIntegralVolume_lt_top v)

/-- The fixed horizontal p-adic Haar measure comapped to a good integral
factor. -/
def padicCliffordGeneralSpinHorizontalIntegralFactorMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Measure.comap
    (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).subtype
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1)

theorem padicCliffordGeneralSpinHorizontalIntegralFactorMeasurableSpace_eq
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    (inferInstance : MeasurableSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)) =
      (@Subtype.instMeasurableSpace
        (V.HeightOnePadicCliffordGeneralSpinGroup v.1)
        (fun g ↦ g ∈ V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
        (inferInstance : MeasurableSpace
          (V.HeightOnePadicCliffordGeneralSpinGroup v.1))) :=
  rfl

@[simp]
theorem padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_univ
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S v Set.univ =
      V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 := by
  change
    (Measure.comap
      (fun g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v =>
        (g.1 : V.HeightOnePadicCliffordGeneralSpinGroup v.1))
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)) Set.univ =
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
        {g | V.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 g}
  simpa using subgroup_comap_measure_univ_eq_of_subtype_mspace
    (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
    (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasurableSpace_eq S v)
    (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).measurableSet

instance padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_isFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    IsFiniteMeasure
      (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S v) where
  measure_univ_lt_top := by
    rw [V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_univ S v]
    exact V.padicCliffordGeneralSpinHorizontalIntegralVolume_lt_top v.1

instance
    padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure.IsMulLeftInvariant
      (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S v) := by
  letI : Measure.IsMulLeftInvariant
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).toIsMulLeftInvariant
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
    (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasurableSpace_eq S v)
    (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).measurableSet

/-- Normalize the good factor by its positive finite literal horizontal
volume. -/
def padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  (V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1)⁻¹ •
    V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S v

@[simp]
theorem
    padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_univ
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v Set.univ = 1 := by
  rw [padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure,
    Measure.smul_apply,
    V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_univ S v]
  exact ENNReal.inv_mul_cancel
    (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero S v)
    (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v.1)

instance
    padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    IsProbabilityMeasure
      (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) :=
  ⟨V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_univ
    S v⟩

instance
    padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure.IsMulLeftInvariant
      (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) := by
  unfold padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
  infer_instance

/-- The normalized local factor pushes to the explicit reciprocal-volume
multiple of the fixed ambient horizontal Haar restriction. -/
theorem map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure.map
        (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).subtype
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) =
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1)⁻¹ •
        (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
            {g | V.PadicCliffordGeneralSpinIsIntegral
              (Rat.HeightOneSpectrum.primesEquiv v.1).1 g} := by
  rw [padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure,
    Measure.map_smul]
  congr 1
  exact subgroup_comap_measure_map_eq_restrict_of_subtype_mspace
    (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
    (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasurableSpace_eq S v)
    (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).measurableSet

end RationalQuadraticSpaceMatrix
