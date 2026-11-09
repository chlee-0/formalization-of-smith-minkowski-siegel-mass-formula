import SMSFormula.RationalFiniteAdeleIntegralLatticeDilation

/-!
# Exact finite quotients of the integral finite-adele lattice

This file converts Haar integrals of functions periodic modulo
`m * Zhat^n` into genuine finite sums on the literal additive quotient.
The quotient carries no chosen residue representatives: equal singleton
masses follow directly from translation invariance, and the already proved
dilation mass supplies the exact factor `m ^ (-n)`.

This is the measure-theoretic reduction needed before comparing the standard
and polar-dual quadratic Gauss integrals.  No quadratic reciprocity value,
local factor, or Weil index is asserted here.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace PositiveDefiniteIntegralLattice

section Generic

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
variable (mu : Measure G) [mu.IsAddLeftInvariant]
variable (H : AddSubgroup G)

theorem measurableSet_quotientAddGroup_singleton
    (hH : MeasurableSet (H : Set G)) (q : G ⧸ H) :
    MeasurableSet ({q} : Set (G ⧸ H)) := by
  induction q using Quotient.inductionOn' with
  | _ x =>
      rw [measurableSet_quotient]
      have heq :
          ((fun y : G ↦ (y : G ⧸ H)) ⁻¹' ({(x : G ⧸ H)} : Set (G ⧸ H))) =
            (fun y : G ↦ -x + y) ⁻¹' (H : Set G) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff,
          QuotientAddGroup.eq_iff_sub_mem]
        simp [sub_eq_add_neg, add_comm]
      rw [heq]
      exact hH.preimage (measurable_const.add measurable_id)

local instance quotientAddGroupMeasurableSingletonClass
    (hH : MeasurableSet (H : Set G)) :
    MeasurableSingletonClass (G ⧸ H) :=
  ⟨measurableSet_quotientAddGroup_singleton H hH⟩

theorem map_quotientAddGroupMk_apply_singleton
    (hH : MeasurableSet (H : Set G)) (q : G ⧸ H) :
    Measure.map (fun y : G ↦ (y : G ⧸ H)) mu {q} = mu H := by
  induction q using Quotient.inductionOn' with
  | _ x =>
      rw [Measure.map_apply
        (f := fun y : G ↦ (y : G ⧸ H))
        QuotientAddGroup.measurable_coe
        (measurableSet_quotientAddGroup_singleton H hH (x : G ⧸ H))]
      have heq :
          (fun y : G ↦ (y : G ⧸ H)) ⁻¹' ({(x : G ⧸ H)} : Set (G ⧸ H)) =
            (fun y : G ↦ -x + y) ⁻¹' (H : Set G) := by
        ext y
        change ((y : G ⧸ H) = (x : G ⧸ H)) ↔ -x + y ∈ H
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simp [sub_eq_add_neg, add_comm]
      rw [heq, measure_preimage_add]

/-- Descend an additive-periodic function to the literal quotient.  The
definition uses the quotient eliminator and therefore stores no section. -/
noncomputable def addQuotientPeriodicLift
    (f : G → ℂ)
    (hperiod : ∀ x z : G, z ∈ H → f (x + z) = f x) :
    (G ⧸ H) → ℂ := fun q ↦
  Quotient.liftOn' q f <| by
    intro x y hxy
    have hz : -x + y ∈ H := QuotientAddGroup.leftRel_apply.mp hxy
    have h := hperiod x (-x + y) hz
    simpa using h.symm

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
@[simp]
theorem addQuotientPeriodicLift_coe
    (f : G → ℂ)
    (hperiod : ∀ x z : G, z ∈ H → f (x + z) = f x)
    (x : G) :
    addQuotientPeriodicLift H f hperiod (x : G ⧸ H) = f x :=
  rfl

variable [H.FiniteIndex] [IsFiniteMeasure mu]

local instance quotientAddGroupFintype : Fintype (G ⧸ H) :=
  AddSubgroup.fintypeQuotientOfFiniteIndex

theorem integral_comp_quotientAddGroupMk_eq_measure_mul_sum
    (hH : MeasurableSet (H : Set G)) (f : (G ⧸ H) → ℂ) :
    ∫ x : G, f (x : G ⧸ H) ∂mu =
      (mu H).toReal * ∑ q : G ⧸ H, f q := by
  letI : MeasurableSingletonClass (G ⧸ H) :=
    quotientAddGroupMeasurableSingletonClass H hH
  have hf_meas : Measurable f := measurable_of_finite f
  have hf_int : Integrable f (Measure.map (fun x : G ↦ (x : G ⧸ H)) mu) := by
    exact Integrable.of_finite
  rw [← integral_map
    (μ := mu) (φ := fun x : G ↦ (x : G ⧸ H))
    QuotientAddGroup.measurable_coe.aemeasurable
    hf_meas.aestronglyMeasurable]
  rw [integral_fintype hf_int]
  unfold Measure.real
  simp_rw [map_quotientAddGroupMk_apply_singleton mu H hH]
  simp only [Complex.real_smul]
  rw [Finset.mul_sum]

end Generic

/-! ## The actual coordinate quotient -/

private theorem measurableSet_integralFiniteAdeleNatDilation_range'
    {m : ℕ} (hm : m ≠ 0) :
    MeasurableSet
      ((integralFiniteAdeleNatDilation m).range : Set IntegralFiniteAdele) := by
  let divide : IntegralFiniteAdele → RationalFiniteAdele := fun x ↦
    algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹) *
      (x : RationalFiniteAdele)
  have hrange :
      ((integralFiniteAdeleNatDilation m).range : Set IntegralFiniteAdele) =
        divide ⁻¹' (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have hyA : m • (y : RationalFiniteAdele) =
          (x : RationalFiniteAdele) := congrArg Subtype.val hy
      change divide x ∈ integralFiniteAdeleSubring
      have hdivide : divide x = (y : RationalFiniteAdele) := by
        dsimp [divide]
        rw [← hyA, nsmul_eq_mul]
        rw [show (m : RationalFiniteAdele) =
          algebraMap ℚ RationalFiniteAdele (m : ℚ) by norm_num]
        rw [← mul_assoc, ← map_mul]
        simp [hm]
      rw [hdivide]
      exact y.property
    · intro hx
      let y : IntegralFiniteAdele := ⟨divide x, hx⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      change m • divide x = (x : RationalFiniteAdele)
      dsimp [divide]
      rw [nsmul_eq_mul]
      rw [show (m : RationalFiniteAdele) =
        algebraMap ℚ RationalFiniteAdele (m : ℚ) by norm_num]
      rw [← mul_assoc, ← map_mul]
      simp [hm]
  rw [hrange]
  exact isOpen_integralFiniteAdeleSubring.measurableSet.preimage
    (continuous_const.mul continuous_subtype_val).measurable

private theorem integralFiniteAdeleCoordinateNatDilation_range_eq_pi'
    (n m : ℕ) :
    ((integralFiniteAdeleCoordinateNatDilation n m).range :
        Set (Fin n → IntegralFiniteAdele)) =
      Set.pi Set.univ
        (fun _ : Fin n ↦
          ((integralFiniteAdeleNatDilation m).range :
            Set IntegralFiniteAdele)) := by
  classical
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i _hi
    exact ⟨y i, rfl⟩
  · intro hx
    choose y hy using fun i ↦ hx i (Set.mem_univ i)
    refine ⟨y, ?_⟩
    funext i
    exact hy i

theorem measurableSet_integralFiniteAdeleCoordinateNatDilation_range
    (n m : ℕ) (hm : m ≠ 0) :
    MeasurableSet
      ((integralFiniteAdeleCoordinateNatDilation n m).range :
        Set (Fin n → IntegralFiniteAdele)) := by
  rw [integralFiniteAdeleCoordinateNatDilation_range_eq_pi']
  exact MeasurableSet.pi Set.countable_univ fun _ _ ↦
    measurableSet_integralFiniteAdeleNatDilation_range' hm

theorem integralFiniteAdeleCoordinateNatDilation_range_index
    (n m : ℕ) (hm : m ≠ 0) :
    (integralFiniteAdeleCoordinateNatDilation n m).range.index = m ^ n := by
  rw [show (integralFiniteAdeleCoordinateNatDilation n m).range =
      AddSubgroup.pi Set.univ
        (fun _ : Fin n ↦ (integralFiniteAdeleNatDilation m).range) by
    apply AddSubgroup.ext
    intro x
    exact Set.ext_iff.mp
      (integralFiniteAdeleCoordinateNatDilation_range_eq_pi' n m) x]
  rw [AddSubgroup.index_pi]
  simp [integralFiniteAdeleNatDilation_range_index m hm]

noncomputable instance integralFiniteAdeleCoordinateNatDilationRangeFiniteIndex
    (n m : ℕ) [NeZero m] :
    (integralFiniteAdeleCoordinateNatDilation n m).range.FiniteIndex :=
  ⟨by
    rw [integralFiniteAdeleCoordinateNatDilation_range_index n m (NeZero.ne m)]
    exact pow_ne_zero n (NeZero.ne m)⟩

noncomputable instance integralFiniteAdeleCoordinateDilationQuotientFintype
    (n m : ℕ) [NeZero m] :
    Fintype ((Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n m).range) :=
  AddSubgroup.fintypeQuotientOfFiniteIndex

noncomputable instance integralFiniteAdeleAddHaarMeasure_isAddLeftInvariant' :
    Measure.IsAddLeftInvariant integralFiniteAdeleAddHaarMeasure := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  exact Measure.IsAddLeftInvariant.comap
    (G := IntegralFiniteAdele)
    rationalFiniteAdeleAddHaarMeasure
    (f := integralFiniteAdeleAddSubgroup.subtype)
    (MeasurableEmbedding.subtype_coe
      isOpen_integralFiniteAdeleSubring.measurableSet)

instance integralFiniteAdeleMeasurableAdd :
    MeasurableAdd₂ IntegralFiniteAdele := by
  constructor
  show Measurable
    (fun p : IntegralFiniteAdele × IntegralFiniteAdele ↦ p.1 + p.2)
  have hfst : Measurable
      (fun p : IntegralFiniteAdele × IntegralFiniteAdele ↦
        (p.1 : RationalFiniteAdele)) :=
    measurable_subtype_coe.comp measurable_fst
  have hsnd : Measurable
      (fun p : IntegralFiniteAdele × IntegralFiniteAdele ↦
        (p.2 : RationalFiniteAdele)) :=
    measurable_subtype_coe.comp measurable_snd
  exact Measurable.subtype_mk (hfst.add hsnd)

noncomputable instance integralFiniteAdeleCoordinateAddHaarMeasure_isAddLeftInvariant
    (n : ℕ) :
    Measure.IsAddLeftInvariant
      (integralFiniteAdeleCoordinateAddHaarMeasure n) := by
  constructor
  intro g
  have h := (measurePreserving_pi
    (fun _ : Fin n ↦ integralFiniteAdeleAddHaarMeasure)
    (fun _ : Fin n ↦ integralFiniteAdeleAddHaarMeasure)
    (fun i ↦ measurePreserving_add_left
      integralFiniteAdeleAddHaarMeasure (g i))).map_eq
  simpa [integralFiniteAdeleCoordinateAddHaarMeasure] using h

noncomputable instance integralFiniteAdeleCoordinateAddHaarMeasure_isProbability
    (n : ℕ) :
    IsProbabilityMeasure (integralFiniteAdeleCoordinateAddHaarMeasure n) :=
  ⟨by simp [integralFiniteAdeleCoordinateAddHaarMeasure]⟩

set_option synthInstance.maxHeartbeats 100000 in
/-- Exact Haar-to-counting conversion on the literal quotient
`Zhat^n / m Zhat^n`.  The function lives on the quotient itself, so the
statement chooses no residue representatives. -/
theorem integralFiniteAdeleCoordinate_integral_comp_quotient_eq
    (n m : ℕ) [NeZero m]
    (f : ((Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n m).range) → ℂ) :
    ∫ x : Fin n → IntegralFiniteAdele,
        f (x : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n m).range)
        ∂integralFiniteAdeleCoordinateAddHaarMeasure n =
      ((((m : ℝ≥0∞)⁻¹) ^ n).toReal : ℂ) * ∑ q, f q := by
  rw [integral_comp_quotientAddGroupMk_eq_measure_mul_sum
    (integralFiniteAdeleCoordinateAddHaarMeasure n)
    (integralFiniteAdeleCoordinateNatDilation n m).range
    (measurableSet_integralFiniteAdeleCoordinateNatDilation_range
      n m (NeZero.ne m)) f]
  rw [integralFiniteAdeleCoordinateAddHaarMeasure_natDilation_range
    n m (NeZero.ne m)]

theorem integralFiniteAdeleCoordinate_integral_comp_quotient_eq_inv_pow
    (n m : ℕ) [NeZero m]
    (f : ((Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n m).range) → ℂ) :
    ∫ x : Fin n → IntegralFiniteAdele,
        f (x : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n m).range)
        ∂integralFiniteAdeleCoordinateAddHaarMeasure n =
      (((m : ℝ) ^ n : ℂ)⁻¹) * ∑ q, f q := by
  rw [integralFiniteAdeleCoordinate_integral_comp_quotient_eq n m f]
  congr 1
  push_cast
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp [inv_pow]

/-- A periodic function on the actual integral finite-adelic coordinate
lattice integrates to the exact normalized sum of its quotient values. -/
theorem integralFiniteAdeleCoordinate_integral_periodic_eq_inv_pow_sum
    (n m : ℕ) [NeZero m]
    (f : (Fin n → IntegralFiniteAdele) → ℂ)
    (hperiod : ∀ x z,
      z ∈ (integralFiniteAdeleCoordinateNatDilation n m).range →
        f (x + z) = f x) :
    ∫ x, f x ∂integralFiniteAdeleCoordinateAddHaarMeasure n =
      (((m : ℝ) ^ n : ℂ)⁻¹) *
        ∑ q, addQuotientPeriodicLift
          (integralFiniteAdeleCoordinateNatDilation n m).range
          f hperiod q := by
  simpa using
    integralFiniteAdeleCoordinate_integral_comp_quotient_eq_inv_pow n m
      (addQuotientPeriodicLift
        (integralFiniteAdeleCoordinateNatDilation n m).range f hperiod)

end PositiveDefiniteIntegralLattice
