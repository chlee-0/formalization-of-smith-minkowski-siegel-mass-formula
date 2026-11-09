import SMSFormula.RationalFiniteAdeleVectorPolarDualLattice

/-!
# Integer dilation of the integral finite adeles

This file records the exact finite-index and Haar-mass calculation for
integer dilates of the everywhere-integral finite adeles.  It is the scalar
measure input for the denominator estimate on the finite quadratic Gauss
integral.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

/-- The everywhere-integral finite adeles, with their additive group
structure. -/
abbrev IntegralFiniteAdele := integralFiniteAdeleAddSubgroup

/-- Multiplication by a natural number on the integral finite adeles. -/
def integralFiniteAdeleNatDilation (m : ℕ) :
    IntegralFiniteAdele →+ IntegralFiniteAdele where
  toFun x := ⟨m • (x : RationalFiniteAdele),
    integralFiniteAdeleAddSubgroup.nsmul_mem x.property m⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem integralFiniteAdeleNatDilation_apply (m : ℕ)
    (x : IntegralFiniteAdele) :
    ((integralFiniteAdeleNatDilation m x : IntegralFiniteAdele) :
        RationalFiniteAdele) = m • (x : RationalFiniteAdele) :=
  rfl

/-- The rational finite-adelic diagonal of an integer, regarded as an
integral finite adele. -/
def integerToIntegralFiniteAdele : ℤ →+ IntegralFiniteAdele where
  toFun z := ⟨algebraMap ℚ RationalFiniteAdele (z : ℚ),
    (rational_mem_integralFiniteAdeleSubring_iff (z : ℚ)).mpr ⟨z, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' z w := by ext; simp

@[simp]
theorem integerToIntegralFiniteAdele_coe (z : ℤ) :
    ((integerToIntegralFiniteAdele z : IntegralFiniteAdele) :
        RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele (z : ℚ) :=
  rfl

/-- An integer diagonal belongs to `m` times the integral finite adeles
exactly when the integer is divisible by `m`. -/
theorem integerToIntegralFiniteAdele_mem_natDilation_range_iff
    {m : ℕ} (hm : m ≠ 0) (z : ℤ) :
    integerToIntegralFiniteAdele z ∈
        (integralFiniteAdeleNatDilation m).range ↔ (m : ℤ) ∣ z := by
  constructor
  · rintro ⟨y, hy⟩
    have hyA :
        m • (y : RationalFiniteAdele) =
          algebraMap ℤ RationalFiniteAdele z := by
      exact congrArg Subtype.val hy
    let q : ℚ := (z : ℚ) / (m : ℚ)
    have hdiag :
        algebraMap ℚ RationalFiniteAdele q =
          (y : RationalFiniteAdele) := by
      calc
        algebraMap ℚ RationalFiniteAdele q =
            algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹) *
              algebraMap ℤ RationalFiniteAdele z := by
                simp [q, div_eq_inv_mul]
        _ = algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹) *
              (m • (y : RationalFiniteAdele)) := by rw [hyA]
        _ = (y : RationalFiniteAdele) := by
          rw [nsmul_eq_mul]
          rw [show (m : RationalFiniteAdele) =
              algebraMap ℚ RationalFiniteAdele (m : ℚ) by norm_num]
          rw [← mul_assoc, ← map_mul]
          simp [hm]
    have hq : algebraMap ℚ RationalFiniteAdele q ∈
        integralFiniteAdeleSubring := by
      rw [hdiag]
      exact y.property
    rcases (rational_mem_integralFiniteAdeleSubring_iff q).mp hq with
      ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hmq : (m : ℚ) * q = z := by
      dsimp [q]
      field_simp
    change (w : ℚ) = q at hw
    have hzwQ : (z : ℚ) = (m : ℚ) * (w : ℚ) := by
      rw [hw]
      exact hmq.symm
    exact_mod_cast hzwQ
  · rintro ⟨w, rfl⟩
    refine ⟨integerToIntegralFiniteAdele w, ?_⟩
    ext
    simp [integralFiniteAdeleNatDilation, nsmul_eq_mul]

/-- Reduction of integer diagonals gives the canonical residue map onto the
quotient of the integral finite adeles by their `m`-dilate. -/
noncomputable def residueToIntegralFiniteAdeleModDilation (m : ℕ) :
    ZMod m →+
      IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range :=
  ZMod.lift m ⟨
    (QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range).comp
      integerToIntegralFiniteAdele,
    by
      apply QuotientAddGroup.eq.mpr
      change -integerToIntegralFiniteAdele (m : ℤ) + 0 ∈
        (integralFiniteAdeleNatDilation m).range
      refine ⟨-integerToIntegralFiniteAdele 1, ?_⟩
      ext
      simp [integralFiniteAdeleNatDilation, nsmul_eq_mul]⟩

@[simp]
theorem residueToIntegralFiniteAdeleModDilation_intCast (m : ℕ) (z : ℤ) :
    residueToIntegralFiniteAdeleModDilation m (z : ZMod m) =
      QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range
        (integerToIntegralFiniteAdele z) := by
  simp [residueToIntegralFiniteAdeleModDilation, ZMod.lift_coe]

theorem residueToIntegralFiniteAdeleModDilation_injective
    {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (residueToIntegralFiniteAdeleModDilation m) := by
  intro r s hrs
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨w, rfl⟩ := ZMod.intCast_surjective s
  rw [residueToIntegralFiniteAdeleModDilation_intCast,
    residueToIntegralFiniteAdeleModDilation_intCast] at hrs
  have hmem :
      -integerToIntegralFiniteAdele z + integerToIntegralFiniteAdele w ∈
        (integralFiniteAdeleNatDilation m).range :=
    QuotientAddGroup.eq.mp hrs
  have hdvd : (m : ℤ) ∣ -z + w :=
    (integerToIntegralFiniteAdele_mem_natDilation_range_iff hm (-z + w)).mp
      (by simpa using hmem)
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub z w m).mpr (by
    simpa [sub_eq_add_neg, add_comm] using hdvd)

theorem residueToIntegralFiniteAdeleModDilation_surjective
    {m : ℕ} (hm : m ≠ 0) :
    Function.Surjective (residueToIntegralFiniteAdeleModDilation m) := by
  intro X
  induction X using Quotient.inductionOn with
  | h x =>
      let a : RationalFiniteAdele :=
        algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹) *
          (x : RationalFiniteAdele)
      obtain ⟨q, hq⟩ :=
        exists_rational_sub_mem_integralFiniteAdeleSubring a
      let u : IntegralFiniteAdele :=
        ⟨a - algebraMap ℚ RationalFiniteAdele q, hq⟩
      have hmu :
          m • (u : RationalFiniteAdele) =
            (x : RationalFiniteAdele) -
              algebraMap ℚ RationalFiniteAdele ((m : ℚ) * q) := by
        dsimp [u, a]
        rw [nsmul_eq_mul, mul_sub]
        have hmcast : (m : RationalFiniteAdele) =
            algebraMap ℚ RationalFiniteAdele (m : ℚ) := by norm_num
        rw [hmcast, ← mul_assoc, ← map_mul, ← map_mul]
        simp [hm]
      have hmq_mem :
          algebraMap ℚ RationalFiniteAdele ((m : ℚ) * q) ∈
            integralFiniteAdeleSubring := by
        have hdiff :
            (x : RationalFiniteAdele) -
                algebraMap ℚ RationalFiniteAdele ((m : ℚ) * q) ∈
              integralFiniteAdeleSubring := by
          rw [← hmu]
          exact integralFiniteAdeleAddSubgroup.nsmul_mem u.property m
        have hid :
            algebraMap ℚ RationalFiniteAdele ((m : ℚ) * q) =
              (x : RationalFiniteAdele) -
                ((x : RationalFiniteAdele) -
                  algebraMap ℚ RationalFiniteAdele ((m : ℚ) * q)) := by
          abel
        rw [hid]
        exact integralFiniteAdeleSubring.sub_mem x.property hdiff
      rcases
          (rational_mem_integralFiniteAdeleSubring_iff ((m : ℚ) * q)).mp
            hmq_mem with ⟨z, hz⟩
      refine ⟨(z : ZMod m), ?_⟩
      rw [residueToIntegralFiniteAdeleModDilation_intCast]
      apply QuotientAddGroup.eq.mpr
      refine ⟨u, ?_⟩
      apply Subtype.ext
      change m • (u : RationalFiniteAdele) =
        -algebraMap ℚ RationalFiniteAdele (z : ℚ) +
          (x : RationalFiniteAdele)
      change (z : ℚ) = (m : ℚ) * q at hz
      rw [hmu, ← hz]
      abel

/-- Residues modulo `m` are exactly the quotient of the integral finite
adeles by their `m`-dilate. -/
noncomputable def residueEquivIntegralFiniteAdeleModDilation
    (m : ℕ) (hm : m ≠ 0) :
    ZMod m ≃+
      IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range :=
  AddEquiv.ofBijective (residueToIntegralFiniteAdeleModDilation m)
    ⟨residueToIntegralFiniteAdeleModDilation_injective hm,
      residueToIntegralFiniteAdeleModDilation_surjective hm⟩

/-- The additive index of `m` times the integral finite adeles is exactly
`m`. -/
theorem integralFiniteAdeleNatDilation_range_index
    (m : ℕ) (hm : m ≠ 0) :
    (integralFiniteAdeleNatDilation m).range.index = m := by
  simpa using Nat.card_congr
    (residueEquivIntegralFiniteAdeleModDilation m hm).symm.toEquiv

/-- The restriction of the normalized finite-adelic additive Haar measure to
the everywhere-integral additive group. -/
noncomputable def integralFiniteAdeleAddHaarMeasure :
    Measure IntegralFiniteAdele :=
  Measure.comap Subtype.val rationalFiniteAdeleAddHaarMeasure

@[simp]
theorem integralFiniteAdeleAddHaarMeasure_univ :
    integralFiniteAdeleAddHaarMeasure Set.univ = 1 := by
  let hval : MeasurableEmbedding
      (integralFiniteAdeleAddSubgroup.subtype :
        IntegralFiniteAdele →+ RationalFiniteAdele) :=
    MeasurableEmbedding.subtype_coe
      isOpen_integralFiniteAdeleSubring.measurableSet
  change (Measure.comap integralFiniteAdeleAddSubgroup.subtype
    rationalFiniteAdeleAddHaarMeasure) Set.univ = 1
  rw [hval.comap_apply, Set.image_univ]
  rw [show Set.range integralFiniteAdeleAddSubgroup.subtype =
      (integralFiniteAdeleSubring : Set RationalFiniteAdele) by
    ext a
    constructor
    · rintro ⟨value, rfl⟩
      exact value.property
    · intro member
      exact ⟨⟨a, member⟩, rfl⟩]
  exact rationalFiniteAdeleAddHaarMeasure_integral

noncomputable instance integralFiniteAdeleAddHaarMeasure_isProbability :
    IsProbabilityMeasure integralFiniteAdeleAddHaarMeasure :=
  ⟨integralFiniteAdeleAddHaarMeasure_univ⟩

local instance integralFiniteAdeleAddHaarMeasure_isAddLeftInvariant :
    Measure.IsAddLeftInvariant integralFiniteAdeleAddHaarMeasure := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  exact Measure.IsAddLeftInvariant.comap
    (G := IntegralFiniteAdele)
    rationalFiniteAdeleAddHaarMeasure
    (f := integralFiniteAdeleAddSubgroup.subtype)
    (MeasurableEmbedding.subtype_coe
      isOpen_integralFiniteAdeleSubring.measurableSet)

private theorem measurableSet_integralFiniteAdeleNatDilation_range
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

/-- With the ambient normalization `vol(Ž) = 1`, the integral finite
adeles divisible by a nonzero natural number `m` have exact mass `m⁻¹`.

This is a global finite-adelic calculation: finite strong approximation
identifies the quotient with `ZMod m`, so bad and dyadic primes are not
discarded or silently renormalized. -/
theorem integralFiniteAdeleAddHaarMeasure_natDilation_range
    (m : ℕ) (hm : m ≠ 0) :
    integralFiniteAdeleAddHaarMeasure
        ((integralFiniteAdeleNatDilation m).range :
          Set IntegralFiniteAdele) =
      (m : ℝ≥0∞)⁻¹ := by
  letI : (integralFiniteAdeleNatDilation m).range.FiniteIndex :=
    ⟨by rw [integralFiniteAdeleNatDilation_range_index m hm]; exact hm⟩
  have hindex := AddSubgroup.index_mul_measure
    (integralFiniteAdeleNatDilation m).range
    (measurableSet_integralFiniteAdeleNatDilation_range hm)
    integralFiniteAdeleAddHaarMeasure
  rw [integralFiniteAdeleNatDilation_range_index m hm,
    integralFiniteAdeleAddHaarMeasure_univ] at hindex
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hindex)

/-- The literal subset `m Ž` of the actual finite-adele carrier. -/
def integralFiniteAdeleNatDilationSet (m : ℕ) : Set RationalFiniteAdele :=
  Set.range fun x : IntegralFiniteAdele ↦
    m • (x : RationalFiniteAdele)

private theorem subtype_image_natDilation_range
    (m : ℕ) :
    (fun x : IntegralFiniteAdele ↦ (x : RationalFiniteAdele)) ''
        ((integralFiniteAdeleNatDilation m).range :
          Set IntegralFiniteAdele) =
      integralFiniteAdeleNatDilationSet m := by
  ext a
  constructor
  · rintro ⟨x, ⟨y, hy⟩, rfl⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    refine ⟨integralFiniteAdeleNatDilation m y, ⟨y, rfl⟩, rfl⟩

private theorem measurableSet_integralFiniteAdeleNatDilationSet
    {m : ℕ} (hm : m ≠ 0) :
    MeasurableSet (integralFiniteAdeleNatDilationSet m) := by
  rw [← subtype_image_natDilation_range]
  exact
    (MeasurableEmbedding.subtype_coe
      isOpen_integralFiniteAdeleSubring.measurableSet).measurableSet_image.mpr
        (measurableSet_integralFiniteAdeleNatDilation_range hm)

/-- In the actual normalized finite-adelic Haar measure, the subset `m Ž`
has exact mass `m⁻¹`. -/
theorem rationalFiniteAdeleAddHaarMeasure_natDilationSet
    (m : ℕ) (hm : m ≠ 0) :
    rationalFiniteAdeleAddHaarMeasure
        (integralFiniteAdeleNatDilationSet m) =
      (m : ℝ≥0∞)⁻¹ := by
  have h := integralFiniteAdeleAddHaarMeasure_natDilation_range m hm
  let hval : MeasurableEmbedding
      (integralFiniteAdeleAddSubgroup.subtype :
        IntegralFiniteAdele →+ RationalFiniteAdele) :=
    MeasurableEmbedding.subtype_coe
      isOpen_integralFiniteAdeleSubring.measurableSet
  change (Measure.comap integralFiniteAdeleAddSubgroup.subtype
      rationalFiniteAdeleAddHaarMeasure)
        ((integralFiniteAdeleNatDilation m).range :
          Set IntegralFiniteAdele) = (m : ℝ≥0∞)⁻¹ at h
  rw [hval.comap_apply] at h
  change rationalFiniteAdeleAddHaarMeasure
      ((fun x : IntegralFiniteAdele ↦ (x : RationalFiniteAdele)) ''
        ((integralFiniteAdeleNatDilation m).range :
          Set IntegralFiniteAdele)) = (m : ℝ≥0∞)⁻¹ at h
  rw [subtype_image_natDilation_range] at h
  exact h

/-! ## Coordinate products -/

/-- Product probability Haar on `n` copies of the integral finite adeles. -/
noncomputable def integralFiniteAdeleCoordinateAddHaarMeasure (n : ℕ) :
    Measure (Fin n → IntegralFiniteAdele) :=
  Measure.pi (fun _ : Fin n ↦ integralFiniteAdeleAddHaarMeasure)

/-- Simultaneous multiplication by `m` in every integral finite-adelic
coordinate. -/
def integralFiniteAdeleCoordinateNatDilation (n m : ℕ) :
    (Fin n → IntegralFiniteAdele) →+ (Fin n → IntegralFiniteAdele) where
  toFun x i := integralFiniteAdeleNatDilation m (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private theorem integralFiniteAdeleCoordinateNatDilation_range_eq_pi
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

/-- Simultaneous divisibility by `m` in `n` integral finite-adelic
coordinates has exact product mass `(m⁻¹)^n`. -/
theorem integralFiniteAdeleCoordinateAddHaarMeasure_natDilation_range
    (n m : ℕ) (hm : m ≠ 0) :
    integralFiniteAdeleCoordinateAddHaarMeasure n
        ((integralFiniteAdeleCoordinateNatDilation n m).range :
          Set (Fin n → IntegralFiniteAdele)) =
      ((m : ℝ≥0∞)⁻¹) ^ n := by
  rw [integralFiniteAdeleCoordinateNatDilation_range_eq_pi,
    integralFiniteAdeleCoordinateAddHaarMeasure, Measure.pi_pi]
  rw [integralFiniteAdeleAddHaarMeasure_natDilation_range m hm]
  simp

/-- The coordinatewise subset `(m Ž)^n` of the actual finite-adelic vector
carrier. -/
def integralFiniteAdeleCoordinateNatDilationSet (n m : ℕ) :
    Set (Fin n → RationalFiniteAdele) :=
  Set.pi Set.univ fun _ : Fin n ↦ integralFiniteAdeleNatDilationSet m

/-- The existing coordinate Haar assigns `(m Ž)^n` the exact mass
`(m⁻¹)^n`. -/
theorem rationalFiniteAdeleCoordinateAddHaarMeasure_natDilationSet
    (n m : ℕ) (hm : m ≠ 0) :
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure n
        (integralFiniteAdeleCoordinateNatDilationSet n m) =
      ((m : ℝ≥0∞)⁻¹) ^ n := by
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure,
    integralFiniteAdeleCoordinateNatDilationSet, Measure.pi_pi]
  rw [rationalFiniteAdeleAddHaarMeasure_natDilationSet m hm]
  simp

end PositiveDefiniteIntegralLattice
