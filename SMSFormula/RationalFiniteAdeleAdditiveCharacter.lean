import SMSFormula.RationalFiniteAdeleStrongApproximation

/-!
# The finite additive character on the rational adeles

This file constructs the finite correction to the positive-sign
archimedean Fourier character.  The algebraic equivalence

`ℚ / ℤ ≃+ 𝔸_ℚ,f / Ẑ`

is sufficient: the target quotient is discrete because `Ẑ` is open, so the
transported character is automatically continuous there and its pullback to
the finite adeles is continuous.

The native quotient topology on `ℚ / ℤ` is deliberately not transported.
Indeed it is not discrete for the ordinary topology on `ℚ`, whereas the
finite-adelic quotient is discrete, so the algebraic equivalence cannot be a
homeomorphism between the two native quotient topologies.
-/

noncomputable section

open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

/-! ## The native quotient-topology obstruction -/

/-- The rational integers are not open in `ℚ` with its ordinary topology. -/
theorem not_isOpen_rationalIntegerAddSubgroup :
    ¬ IsOpen (rationalIntegerAddSubgroup : Set ℚ) := by
  intro hopen
  have hzero : (0 : ℚ) ∈ rationalIntegerAddSubgroup := by
    simp [rationalIntegerAddSubgroup]
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hzero)
  let q : ℚ := min (u / 2) (1 / 2)
  have hqpos : 0 < q := by
    exact lt_min (half_pos hu) (by norm_num)
  have hqu : q < u := by
    exact (min_le_left _ _).trans_lt (half_lt_self hu)
  have hqone : q < 1 := by
    exact (min_le_right _ _).trans_lt (by norm_num)
  have hqmem : q ∈ rationalIntegerAddSubgroup :=
    hlu ⟨hl.trans hqpos, hqu⟩
  change q ∈ (algebraMap ℤ ℚ).range at hqmem
  obtain ⟨z, hz⟩ := hqmem
  change (z : ℚ) = q at hz
  rw [← hz] at hqpos hqone
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hqpos
  have hzone : z < (1 : ℤ) := by exact_mod_cast hqone
  omega

/-- The native quotient topology on `ℚ / ℤ` is not discrete. -/
theorem not_discreteTopology_rationalModInteger :
    ¬ DiscreteTopology RationalModInteger := by
  intro hdiscrete
  exact not_isOpen_rationalIntegerAddSubgroup
    (QuotientAddGroup.discreteTopology_iff.mp hdiscrete)

/-- The native quotient topology on `𝔸_ℚ,f / Ẑ` is discrete because `Ẑ` is
open in the restricted-product topology. -/
theorem discreteTopology_rationalFiniteAdeleModIntegral :
    DiscreteTopology RationalFiniteAdeleModIntegral := by
  apply QuotientAddGroup.discreteTopology
  simpa [integralFiniteAdeleAddSubgroup] using
    isOpen_integralFiniteAdeleSubring

/-- There is no homeomorphism between the two native quotient topologies.
In particular, the strong-approximation additive equivalence must not be
upgraded by transporting the ordinary topology of `ℚ / ℤ`. -/
theorem isEmpty_homeomorph_rationalModInteger_rationalFiniteAdeleModIntegral :
    IsEmpty (RationalModInteger ≃ₜ RationalFiniteAdeleModIntegral) := by
  constructor
  intro e
  exact not_discreteTopology_rationalModInteger
    ((e.discreteTopology_iff).mpr
      discreteTopology_rationalFiniteAdeleModIntegral)

/-! ## The inverse rational phase and its finite-adelic transport -/

/-- The inverse of the positive-sign real Fourier phase on rational scalars. -/
noncomputable def rationalInverseFourierChar : AddChar ℚ Circle :=
  (Real.fourierChar.compAddMonoidHom
    (algebraMap ℚ ℝ).toAddMonoidHom)⁻¹

@[simp]
theorem rationalInverseFourierChar_apply (q : ℚ) :
    rationalInverseFourierChar q = (Real.fourierChar (q : ℝ))⁻¹ := by
  simpa [rationalInverseFourierChar] using
    (Real.fourierChar.map_neg_eq_inv (q : ℝ))

/-- The inverse rational phase is trivial on integers. -/
@[simp]
theorem rationalInverseFourierChar_intCast (z : ℤ) :
    rationalInverseFourierChar (z : ℚ) = 1 := by
  rw [rationalInverseFourierChar_apply]
  change (Circle.exp (2 * Real.pi * (z : ℝ)))⁻¹ = 1
  rw [Circle.exp_two_pi_mul_int, inv_one]

/-- The inverse rational phase has exactly the rational integers as its
kernel. -/
theorem rationalInverseFourierChar_eq_one_iff
    (q : ℚ) :
    rationalInverseFourierChar q = 1 ↔
      q ∈ rationalIntegerAddSubgroup := by
  rw [rationalInverseFourierChar_apply, inv_eq_one]
  change Circle.exp (2 * Real.pi * (q : ℝ)) = 1 ↔ _
  rw [Circle.exp_eq_one]
  constructor
  · rintro ⟨z, hz⟩
    change q ∈ (algebraMap ℤ ℚ).range
    refine ⟨z, ?_⟩
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hcast : (q : ℝ) = (z : ℝ) := by
      apply mul_left_cancel₀ htwoPi
      calc
        (2 * Real.pi) * (q : ℝ) = 2 * Real.pi * (q : ℝ) := rfl
        _ = (z : ℝ) * (2 * Real.pi) := hz
        _ = (2 * Real.pi) * (z : ℝ) := by ring
    exact_mod_cast hcast.symm
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    simp [algebraMap_int_eq, mul_comm, mul_left_comm]

/-- The inverse real phase descends algebraically to `ℚ / ℤ`.  No topology on
this quotient is used in the construction. -/
noncomputable def rationalModIntegerInverseFourierChar :
    AddChar RationalModInteger Circle :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift rationalIntegerAddSubgroup
      rationalInverseFourierChar.toAddMonoidHom (by
        rintro q ⟨z, rfl⟩
        simpa using congrArg Additive.ofMul
          (rationalInverseFourierChar_intCast z)))

@[simp]
theorem rationalModIntegerInverseFourierChar_mk (q : ℚ) :
    rationalModIntegerInverseFourierChar
        (QuotientAddGroup.mk' rationalIntegerAddSubgroup q) =
      rationalInverseFourierChar q :=
  rfl

/-- The descended rational phase is faithful on the algebraic quotient
`ℚ / ℤ`. -/
theorem rationalModIntegerInverseFourierChar_eq_one_iff
    (x : RationalModInteger) :
    rationalModIntegerInverseFourierChar x = 1 ↔ x = 0 := by
  induction x using Quotient.inductionOn with
  | h q =>
      change rationalModIntegerInverseFourierChar
          (QuotientAddGroup.mk' rationalIntegerAddSubgroup q) = 1 ↔
        QuotientAddGroup.mk' rationalIntegerAddSubgroup q = 0
      rw [rationalModIntegerInverseFourierChar_mk,
        rationalInverseFourierChar_eq_one_iff]
      exact (QuotientAddGroup.eq_zero_iff q).symm

/-- Transport the inverse rational phase across the certified algebraic
strong-approximation equivalence. -/
noncomputable def rationalFiniteAdeleModIntegralFourierChar :
    AddChar RationalFiniteAdeleModIntegral Circle :=
  rationalModIntegerInverseFourierChar.compAddMonoidHom
    rationalModIntegerEquivFiniteAdeleModIntegral.symm.toAddMonoidHom

@[simp]
theorem rationalFiniteAdeleModIntegralFourierChar_equiv_apply
    (x : RationalModInteger) :
    rationalFiniteAdeleModIntegralFourierChar
        (rationalModIntegerEquivFiniteAdeleModIntegral x) =
      rationalModIntegerInverseFourierChar x := by
  change rationalModIntegerInverseFourierChar
      (rationalModIntegerEquivFiniteAdeleModIntegral.symm
        (rationalModIntegerEquivFiniteAdeleModIntegral x)) = _
  rw [rationalModIntegerEquivFiniteAdeleModIntegral.symm_apply_apply]

/-- The transported character is faithful on the finite-adelic quotient. -/
theorem rationalFiniteAdeleModIntegralFourierChar_eq_one_iff
    (x : RationalFiniteAdeleModIntegral) :
    rationalFiniteAdeleModIntegralFourierChar x = 1 ↔ x = 0 := by
  change rationalModIntegerInverseFourierChar
      (rationalModIntegerEquivFiniteAdeleModIntegral.symm x) = 1 ↔ x = 0
  rw [rationalModIntegerInverseFourierChar_eq_one_iff]
  simp

/-- The character on the native finite-adelic quotient is continuous because
that quotient is discrete. -/
theorem continuous_rationalFiniteAdeleModIntegralFourierChar :
    Continuous rationalFiniteAdeleModIntegralFourierChar := by
  letI : DiscreteTopology RationalFiniteAdeleModIntegral :=
    discreteTopology_rationalFiniteAdeleModIntegral
  exact continuous_of_discreteTopology

/-- Pull the quotient character back to the actual restricted-product finite
adeles. -/
noncomputable def rationalFiniteAdeleFourierChar :
    AddChar RationalFiniteAdele Circle :=
  rationalFiniteAdeleModIntegralFourierChar.compAddMonoidHom
    (QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup)

/-- The finite-adelic correction is continuous. -/
theorem continuous_rationalFiniteAdeleFourierChar :
    Continuous rationalFiniteAdeleFourierChar :=
  continuous_rationalFiniteAdeleModIntegralFourierChar.comp
    QuotientAddGroup.continuous_mk

/-- The finite character is trivial on every everywhere-integral finite
adele. -/
@[simp]
theorem rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    (a : RationalFiniteAdele) (ha : a ∈ integralFiniteAdeleSubring) :
    rationalFiniteAdeleFourierChar a = 1 := by
  change rationalFiniteAdeleModIntegralFourierChar
      (QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup a) = 1
  have hzero :
      QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup a = 0 := by
    apply (QuotientAddGroup.eq_zero_iff a).2
    simpa [integralFiniteAdeleAddSubgroup] using ha
  rw [hzero]
  exact AddChar.map_zero_eq_one _

/-- The finite character has exactly the everywhere-integral finite adeles
as its kernel. -/
@[simp]
theorem rationalFiniteAdeleFourierChar_eq_one_iff
    (a : RationalFiniteAdele) :
    rationalFiniteAdeleFourierChar a = 1 ↔
      a ∈ integralFiniteAdeleSubring := by
  change rationalFiniteAdeleModIntegralFourierChar
      (QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup a) = 1 ↔ _
  rw [rationalFiniteAdeleModIntegralFourierChar_eq_one_iff]
  change QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup a = 0 ↔
    a ∈ integralFiniteAdeleAddSubgroup
  exact QuotientAddGroup.eq_zero_iff a

/-- On every rational diagonal point, the finite character is exactly the
inverse positive archimedean phase. -/
@[simp]
theorem rationalFiniteAdeleFourierChar_algebraMap (q : ℚ) :
    rationalFiniteAdeleFourierChar
        (algebraMap ℚ RationalFiniteAdele q) =
      (Real.fourierChar (q : ℝ))⁻¹ := by
  calc
    rationalFiniteAdeleFourierChar
        (algebraMap ℚ RationalFiniteAdele q) =
        rationalFiniteAdeleModIntegralFourierChar
          (QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup
            (algebraMap ℚ RationalFiniteAdele q)) := rfl
    _ = rationalFiniteAdeleModIntegralFourierChar
          (rationalModIntegerEquivFiniteAdeleModIntegral
            (QuotientAddGroup.mk' rationalIntegerAddSubgroup q)) := by
      rw [rationalModIntegerEquivFiniteAdeleModIntegral_apply,
        rationalModIntegerToFiniteAdeleModIntegral_mk]
    _ = rationalModIntegerInverseFourierChar
          (QuotientAddGroup.mk' rationalIntegerAddSubgroup q) :=
      rationalFiniteAdeleModIntegralFourierChar_equiv_apply _
    _ = rationalInverseFourierChar q :=
      rationalModIntegerInverseFourierChar_mk q
    _ = (Real.fourierChar (q : ℝ))⁻¹ :=
      rationalInverseFourierChar_apply q

/-! ## The global rational-adelic character -/

/-- The finite correction pulled back along the finite projection of the full
rational adele ring. -/
noncomputable def rationalAdeleFiniteFourierChar :
    AddChar RationalAdele Circle :=
  rationalFiniteAdeleFourierChar.compAddMonoidHom
    (RingHom.snd RationalInfiniteAdele RationalFiniteAdele).toAddMonoidHom

@[simp]
theorem rationalAdeleFiniteFourierChar_apply (x : RationalAdele) :
    rationalAdeleFiniteFourierChar x = rationalFiniteAdeleFourierChar x.2 :=
  rfl

/-- The finite correction on the full rational adeles is continuous. -/
theorem continuous_rationalAdeleFiniteFourierChar :
    Continuous rationalAdeleFiniteFourierChar :=
  continuous_rationalFiniteAdeleFourierChar.comp continuous_snd

private theorem rationalAdele_algebraMap_snd (q : ℚ) :
    (algebraMap ℚ RationalAdele q).2 =
      algebraMap ℚ RationalFiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele)) q

/-- The full-adele finite factor has the required inverse phase on rational
diagonal points. -/
@[simp]
theorem rationalAdeleFiniteFourierChar_algebraMap (q : ℚ) :
    rationalAdeleFiniteFourierChar (algebraMap ℚ RationalAdele q) =
      (Real.fourierChar (q : ℝ))⁻¹ := by
  rw [rationalAdeleFiniteFourierChar_apply,
    rationalAdele_algebraMap_snd,
    rationalFiniteAdeleFourierChar_algebraMap]

/-- The global rational-adelic Fourier character is the product of the fixed
positive archimedean phase and the finite correction. -/
noncomputable def rationalAdeleFourierChar : AddChar RationalAdele Circle :=
  rationalAdeleArchimedeanFourierChar * rationalAdeleFiniteFourierChar

@[simp]
theorem rationalAdeleFourierChar_apply (x : RationalAdele) :
    rationalAdeleFourierChar x =
      rationalAdeleArchimedeanFourierChar x *
        rationalFiniteAdeleFourierChar x.2 :=
  rfl

/-- The global rational-adelic character is continuous. -/
theorem continuous_rationalAdeleFourierChar :
    Continuous rationalAdeleFourierChar :=
  continuous_rationalAdeleArchimedeanFourierChar.mul
    continuous_rationalAdeleFiniteFourierChar

/-- The global character is literally trivial on every rational diagonal
point: the finite phase cancels the positive archimedean phase. -/
@[simp]
theorem rationalAdeleFourierChar_algebraMap (q : ℚ) :
    rationalAdeleFourierChar (algebraMap ℚ RationalAdele q) = 1 := by
  rw [rationalAdeleFourierChar, AddChar.mul_apply,
    rationalAdeleArchimedeanFourierChar_algebraMap,
    rationalAdeleFiniteFourierChar_algebraMap]
  simp

end PositiveDefiniteIntegralLattice
