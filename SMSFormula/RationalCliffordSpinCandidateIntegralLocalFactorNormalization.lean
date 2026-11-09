import SMSFormula.RationalCliffordSpinCandidateLocalCompactnessPrecursor
import SMSFormula.RationalCliffordSpinCandidatePlacewiseHaar
import SMSFormula.AdelicDoubleCosets

/-!
# Normalized integral local factors for the Clifford--Spin candidate

For a normalized finite exceptional set `S`, a place outside
`cliffordSpinCandidateAdmissibleExceptionalPlaces S` has the literal
point-and-inverse integral-coordinate locus as its local factor.  The earlier
compactness layer proves this subgroup compact-open, while the placewise Haar
layer supplies a full p-adic Haar measure transported from the local `SO`
differential scale.

This file records the literal mass of the integral locus, proves it positive
and finite at every such good place, and normalizes the comapped subgroup
measure to a left-invariant probability measure.  The good-place hypothesis is
stored in the index type: at a bad place the chosen rational Clifford
coordinate presentation need not make the raw integral locus a subgroup.

The construction keeps its reciprocal-volume scalar explicit.  It does not
form an infinite product, compare with the full-adelic reference Haar scale,
or identify the transported scale analytically with the chosen Spin top form.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open TopologicalSpace
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance cliffordSpinIntegralLocalFactorPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cliffordSpinIntegralLocalFactorGroupMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance cliffordSpinIntegralLocalFactorGroupBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

/-! ## Good-place carrier -/

/-- A height-one place outside the normalized exceptional set. -/
abbrev CliffordSpinCandidateAdmissibleIntegralPlace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  {v : IsDedekindDomain.HeightOneSpectrum ℤ //
    v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S}

/-- The integral local subgroup at a good place of the normalized block. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :=
  V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v.1

/-- Inclusion of a good integral local factor in the unrestricted local Spin
candidate group. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v →*
      V.HeightOnePadicCliffordSpinCandidateGroup v.1 :=
  (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
    S v.1).subtype

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
        S v g = g.1 :=
  rfl

theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
        S v) :=
  continuous_subtype_val

/-! ## Literal chart-glued Haar volume -/

/-- The literal mass of the point-and-inverse integral-coordinate locus for
the completed chart-glued p-adic Spin Haar measure. -/
def heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0∞ :=
  V.padicCliffordSpinCandidateChartGluedMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
    {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v g}

/-- The literal integral-coordinate locus has finite chart-glued Haar mass. -/
theorem heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_lt_top
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v < ⊤ := by
  let μ :=
    V.padicCliffordSpinCandidateChartGluedMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : IsFiniteMeasureOnCompacts μ :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isFiniteOnCompacts
      (Rat.HeightOneSpectrum.primesEquiv v).1
  exact
    (V.isCompact_heightOnePadicCliffordSpinCandidateIsIntegral v).measure_lt_top

/-- At a good place, the literal integral-coordinate locus has positive
chart-glued Haar mass. -/
theorem heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    0 < V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 := by
  let μ :=
    V.padicCliffordSpinCandidateChartGluedMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI : Measure.IsOpenPosMeasure μ :=
    (V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).toIsOpenPosMeasure
  have hone :
      (1 : V.HeightOnePadicCliffordSpinCandidateGroup v.1) ∈
        {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g} := by
    rw [← V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor_carrier_eq_integral
      S v.1 v.2]
    exact Subgroup.one_mem _
  exact
    (V.isOpen_heightOnePadicCliffordSpinCandidateIsIntegral v.1).measure_pos μ
      ⟨1, hone⟩

theorem heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 ≠ 0 :=
  ne_of_gt
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_pos S v)

theorem heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v ≠ ⊤ :=
  ne_of_lt
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_lt_top v)

/-! ## Comapped and normalized local-factor measures -/

/-- The chart-glued p-adic Haar measure comapped to a good integral local
factor. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  Measure.comap
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
      S v)
    (V.padicCliffordSpinCandidateChartGluedMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1)

/-- The good local factor has the inherited subtype measurable space. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasurableSpace_eq
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (inferInstance : MeasurableSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v)) =
      (@Subtype.instMeasurableSpace
        (V.HeightOnePadicCliffordSpinCandidateGroup v.1)
        (fun g ↦ g ∈
          V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
            S v.1)
        (inferInstance : MeasurableSpace
          (V.HeightOnePadicCliffordSpinCandidateGroup v.1))) :=
  rfl

/-- The comapped local-factor measure has the literal integral-locus mass. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_univ
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v Set.univ =
      V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 := by
  change
    (Measure.comap
      (fun g :
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v ↦
        (g.1 : V.HeightOnePadicCliffordSpinCandidateGroup v.1))
      (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)) Set.univ =
      (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
        {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g}
  rw [subgroup_comap_measure_univ_eq_of_subtype_mspace
    (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
      S v.1)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasurableSpace_eq
      S v)
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
      S v.1 v.2).measurableSet]
  rw [V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor_carrier_eq_integral
    S v.1 v.2]

instance
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_isFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v) where
  measure_univ_lt_top := by
    rw [V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_univ
      S v]
    exact
      V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_lt_top v.1

instance
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v) := by
  letI : Measure.IsMulLeftInvariant
      (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isMulLeftInvariant
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  exact
    subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
      (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v.1)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasurableSpace_eq
        S v)
      (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v.1 v.2).measurableSet

/-- Normalize the good integral-factor measure by its positive finite literal
chart-glued Haar mass. -/
def finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1)⁻¹ •
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure S v

/-- The normalized good local factor has total mass one. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_univ
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S v Set.univ = 1 := by
  rw [finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure,
    Measure.smul_apply,
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_univ
      S v]
  exact ENNReal.inv_mul_cancel
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero S v)
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v.1)

instance
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S v) where
  measure_univ :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_univ
      S v

instance
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S v) := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
  infer_instance

/-- Before taking products, the comapped good-factor measure is its literal
volume times the normalized probability measure. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_eq_volume_smul_normalized
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v =
      V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 •
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v := by
  rw [finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure,
    ← smul_assoc]
  simp only [smul_eq_mul]
  rw [ENNReal.mul_inv_cancel
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero S v)
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v.1),
    one_smul]

/-- The unnormalized good-factor measure pushes forward to ambient chart-glued
Haar restricted to the literal integral-coordinate locus. -/
theorem
    map_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
          S v)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
          S v) =
      (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
          {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g} := by
  rw [show
      (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
          {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g} =
        (V.padicCliffordSpinCandidateChartGluedMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
            (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
              S v.1 : Set
                (V.HeightOnePadicCliffordSpinCandidateGroup v.1)) by
      rw [V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor_carrier_eq_integral
        S v.1 v.2]]
  exact
    subgroup_comap_measure_map_eq_restrict_of_subtype_mspace
      (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v.1)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasurableSpace_eq
        S v)
      (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v.1 v.2).measurableSet

/-- The normalized good-factor measure pushes forward to the explicitly
rescaled ambient restriction. -/
theorem
    map_finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
          S v)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) =
      (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1)⁻¹ •
        (V.padicCliffordSpinCandidateChartGluedMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
            {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g} := by
  rw [finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure,
    Measure.map_smul,
    V.map_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
      S v]

end RationalQuadraticSpaceMatrix
