import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockCarrier
import SMSFormula.RationalSpecialOrthogonalInvariantDifferentialPlacewiseGroupMeasure

/-!
# Normalized integral local factors for the rational invariant differential

For an arbitrary rational quadratic-space matrix `V` and height-one place
`v` of `ℤ`, the integral local special-orthogonal subgroup was defined by
requiring both the matrix and its inverse to have integral entries after
transport to the height-one completion field.

This module identifies that subgroup with the preimage of the standard
p-adic integral matrix units.  It is therefore compact-open.  Its literal
mass for the p-adic group measure induced by `V.invariantTopDifferential` is
positive and finite.

The ambient differential Haar measure is also comapped to the integral
subgroup and divided by that literal mass.  The resulting local measure is a
left-invariant probability measure.  No product, finite-adelic measure, or
adelic normalization is constructed.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Matrix
open TopologicalSpace
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance integralLocalFactorPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance integralLocalFactorGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance integralLocalFactorGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

/-! ## Comparison with standard integral matrix units -/

/-- The local integral special-orthogonal subgroup is the preimage of the
standard p-adic integral matrix units under the two ambient subtype maps. -/
theorem heightOnePadicSpecialOrthogonalIntegralSubgroup_eq_comap
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicSpecialOrthogonalIntegralSubgroup v =
      (localPadicIntegralMatrixUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 n).comap
        ((formPreservingMatrixSubgroup
            (V.pairingMatrix.map
              (algebraMap ℚ
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))).subtype.comp
          (specialFormPreservingMatrixSubgroup
            (V.pairingMatrix.map
              (algebraMap ℚ
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))).subtype) := by
  ext g
  rw [mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff]
  change
    V.HeightOnePadicSpecialOrthogonalIsIntegral v g ↔
      (∀ i j, g.1.1.1 i j ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
      (∀ i j, (g.1.1⁻¹).1 i j ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
  constructor
  · intro hg
    constructor
    · intro i j
      have hij := hg.1 i j
      rw [mem_adicCompletionIntegers_iff_padic] at hij
      simpa using hij
    · intro i j
      have hij := hg.2 i j
      rw [mem_adicCompletionIntegers_iff_padic] at hij
      simpa using hij
  · rintro ⟨hg, hginv⟩
    constructor
    · intro i j
      rw [mem_adicCompletionIntegers_iff_padic]
      simpa using hg i j
    · intro i j
      rw [mem_adicCompletionIntegers_iff_padic]
      simpa using hginv i j

/-- Membership in the general integral local factor can equivalently be
checked directly in the standard p-adic integer ring. -/
theorem mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicSpecialOrthogonalGroup v) :
    g ∈ V.heightOnePadicSpecialOrthogonalIntegralSubgroup v ↔
      (∀ i j, g.1.1.1 i j ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
      (∀ i j, (g.1.1⁻¹).1 i j ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  rw [V.heightOnePadicSpecialOrthogonalIntegralSubgroup_eq_comap v]
  rfl

private theorem isClosed_heightOnePadicFormPreservingSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsClosed
      (formPreservingMatrixSubgroup
          (V.pairingMatrix.map
            (algebraMap ℚ
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
        Set
          (Matrix (Fin n) (Fin n)
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ) := by
  change IsClosed
    {g : (Matrix (Fin n) (Fin n)
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ |
      g.1ᵀ *
          V.pairingMatrix.map
            (algebraMap ℚ
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) *
          g.1 =
        V.pairingMatrix.map
          (algebraMap ℚ
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])}
  have hcontinuous : Continuous
      (fun g : (Matrix (Fin n) (Fin n)
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ ↦
        g.1ᵀ *
          V.pairingMatrix.map
            (algebraMap ℚ
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) *
          g.1) := by
    fun_prop
  exact isClosed_eq hcontinuous continuous_const

private theorem isClosed_heightOnePadicSpecialSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsClosed
      (specialFormPreservingMatrixSubgroup
          (V.pairingMatrix.map
            (algebraMap ℚ
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
        Set
          (formPreservingMatrixSubgroup
            (V.pairingMatrix.map
              (algebraMap ℚ
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])))) := by
  have hset :
      (specialFormPreservingMatrixSubgroup
          (V.pairingMatrix.map
            (algebraMap ℚ
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
        Set
          (formPreservingMatrixSubgroup
            (V.pairingMatrix.map
              (algebraMap ℚ
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])))) =
        {g |
          g.1.1.det = 1} := by
    ext g
    exact
      mem_specialFormPreservingMatrixSubgroup_iff
        (V.pairingMatrix.map
          (algebraMap ℚ
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) g
  rw [hset]
  exact isClosed_eq
    ((Units.continuous_val.comp continuous_subtype_val).matrix_det)
    continuous_const

/-- The carrier-independent integral local special-orthogonal factor is
open. -/
theorem isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsOpen
      (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
        Set (V.HeightOnePadicSpecialOrthogonalGroup v)) := by
  rw [V.heightOnePadicSpecialOrthogonalIntegralSubgroup_eq_comap v]
  exact
    (isOpen_localPadicIntegralMatrixUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1 n).preimage
        (continuous_subtype_val.comp continuous_subtype_val)

/-- The carrier-independent integral local special-orthogonal factor is
compact. -/
theorem isCompact_heightOnePadicSpecialOrthogonalIntegralSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsCompact
      (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
        Set (V.HeightOnePadicSpecialOrthogonalGroup v)) := by
  have hspecial :=
    (isClosed_heightOnePadicSpecialSubgroup V v)
      |>.isClosedEmbedding_subtypeVal
  have hform :=
    (isClosed_heightOnePadicFormPreservingSubgroup V v)
      |>.isClosedEmbedding_subtypeVal
  let hembedding := hform.comp hspecial
  rw [V.heightOnePadicSpecialOrthogonalIntegralSubgroup_eq_comap v]
  exact hembedding.isCompact_preimage
    (isCompact_localPadicIntegralMatrixUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1 n)

/-! ## Literal differential volume -/

/-- The literal invariant-differential mass of the integral local
special-orthogonal factor. -/
def heightOnePadicSpecialOrthogonalIntegralVolume
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0∞ :=
  V.padicInvariantDifferentialGroupMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
    (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
      Set (V.HeightOnePadicSpecialOrthogonalGroup v))

/-- The invariant-differential mass of the integral local factor is finite. -/
theorem heightOnePadicSpecialOrthogonalIntegralVolume_lt_top
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicSpecialOrthogonalIntegralVolume v < ⊤ := by
  let μ :=
    V.padicInvariantDifferentialGroupMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : IsFiniteMeasureOnCompacts μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isFiniteOnCompacts
      (Rat.HeightOneSpectrum.primesEquiv v).1 n
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  exact
    (V.isCompact_heightOnePadicSpecialOrthogonalIntegralSubgroup v)
      |>.measure_lt_top

/-- The invariant-differential mass of the integral local factor is
strictly positive. -/
theorem heightOnePadicSpecialOrthogonalIntegralVolume_pos
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    0 < V.heightOnePadicSpecialOrthogonalIntegralVolume v := by
  let μ :=
    V.padicInvariantDifferentialGroupMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : Measure.IsOpenPosMeasure μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isOpenPosMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1 n
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  exact
    (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v)
      |>.measure_pos μ
        ⟨1, Subgroup.one_mem _⟩

theorem heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicSpecialOrthogonalIntegralVolume v ≠ 0 :=
  ne_of_gt (V.heightOnePadicSpecialOrthogonalIntegralVolume_pos v)

theorem heightOnePadicSpecialOrthogonalIntegralVolume_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicSpecialOrthogonalIntegralVolume v ≠ ⊤ :=
  ne_of_lt (V.heightOnePadicSpecialOrthogonalIntegralVolume_lt_top v)

/-! ## The normalized subgroup measure -/

/-- The ambient invariant-differential Haar measure comapped to the integral
local factor. -/
def heightOnePadicSpecialOrthogonalIntegralMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  Measure.comap
    (fun g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v ↦
      (g : V.HeightOnePadicSpecialOrthogonalGroup v))
    (V.padicInvariantDifferentialGroupMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1)

/-- The integral local factor has the inherited subtype measurable space. -/
theorem heightOnePadicSpecialOrthogonalIntegralMeasurableSpace_eq
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (inferInstance :
      MeasurableSpace
        (V.HeightOnePadicSpecialOrthogonalIntegralGroup v)) =
      (@Subtype.instMeasurableSpace
        (V.HeightOnePadicSpecialOrthogonalGroup v)
        (fun g ↦
          g ∈ V.heightOnePadicSpecialOrthogonalIntegralSubgroup v)
        (inferInstance :
          MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v))) :=
  rfl

/-- The total comapped mass is the literal ambient integral-factor volume. -/
@[simp]
theorem heightOnePadicSpecialOrthogonalIntegralMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicSpecialOrthogonalIntegralMeasure v Set.univ =
      V.heightOnePadicSpecialOrthogonalIntegralVolume v := by
  change
    (Measure.comap
      (fun g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v ↦
        (g : V.HeightOnePadicSpecialOrthogonalGroup v))
      (V.padicInvariantDifferentialGroupMeasure
        (Rat.HeightOneSpectrum.primesEquiv v).1)) Set.univ =
      _
  rw [subgroup_comap_measure_univ_eq_of_subtype_mspace
    (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v)
    (V.heightOnePadicSpecialOrthogonalIntegralMeasurableSpace_eq v)
    (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v).measurableSet]
  rfl

instance heightOnePadicSpecialOrthogonalIntegralMeasure_isFinite
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsFiniteMeasure
      (V.heightOnePadicSpecialOrthogonalIntegralMeasure v) where
  measure_univ_lt_top := by
    rw [V.heightOnePadicSpecialOrthogonalIntegralMeasure_univ v]
    exact V.heightOnePadicSpecialOrthogonalIntegralVolume_lt_top v

instance heightOnePadicSpecialOrthogonalIntegralMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsMulLeftInvariant
      (V.heightOnePadicSpecialOrthogonalIntegralMeasure v) := by
  letI : Measure.IsMulLeftInvariant
      (V.padicInvariantDifferentialGroupMeasure
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    (V.padicInvariantDifferentialGroupMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1).toIsMulLeftInvariant
  exact
    subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
      (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v)
      (V.heightOnePadicSpecialOrthogonalIntegralMeasurableSpace_eq v)
      (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v).measurableSet

/-- Normalize the integral-factor differential measure by its positive finite
total mass. -/
def heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ •
    V.heightOnePadicSpecialOrthogonalIntegralMeasure v

/-- The normalized integral-factor measure has total mass one. -/
@[simp]
theorem heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v Set.univ =
      1 := by
  rw [
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure,
    Measure.smul_apply,
    V.heightOnePadicSpecialOrthogonalIntegralMeasure_univ v]
  exact ENNReal.inv_mul_cancel
    (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v)
    (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v)

instance heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isProbability
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsProbabilityMeasure
      (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v) where
  measure_univ :=
    V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_univ v

instance
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsMulLeftInvariant
      (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v) := by
  unfold heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
  infer_instance

end RationalQuadraticSpaceMatrix
