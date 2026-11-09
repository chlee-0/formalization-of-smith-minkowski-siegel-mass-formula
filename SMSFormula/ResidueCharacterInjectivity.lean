import SMSFormula.LocalPhaseIntegralBound

/-!
# Injectivity of the residue character, and the reciprocal frequency

The local-integral bound needs exactly one hypothesis: injectivity of the residue character.  By the
zero-frequency counterexample it is a condition on the frequency `t`, and this file identifies that
condition exactly and exhibits a frequency satisfying it at every conductor.

The condition is exactness of the conductor.  The conductor condition says `t * m` is integral --
that `t` clears the level.  Injectivity says it clears nothing smaller: whenever `t * r` is integral
at an integral `r`, already `r` is an `m`-multiple.  The equivalence is the character's exact
kernel: the finite Fourier character used here is trivial on the integral finite adeles and on
nothing else, so the residue character's kernel is exactly the residues of such `r`.

The witness is the reciprocal `1/m`, and it costs one line in each direction: `(1/m) * m = 1` is
integral, and if `(1/m) * r` is integral then `r = m * ((1/m) * r)` is visibly an `m`-multiple.
Since `m` is a unit in the finite adeles, no denominator-clearing argument is needed anywhere.

Consequently, for the reciprocal family the local integrals of the frequency phase are summable
against the totient multiplicity above rank four, with no further hypothesis.

Scope.  Injectivity is a real restriction and not a formality: the zero frequency clears every
conductor and its residue character is the trivial one, which is not injective beyond `m = 1`.
Nothing here evaluates a Gauss sum; the bound remains an inequality, and the
good-prime/exceptional-prime split is not performed -- the reciprocal frequency simply has exact
conductor at every `m`, so no split arises for it.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix

variable {n : ℕ}

/-! ## The character's exact kernel, complexified -/

/-- The complex character is trivial exactly on the integral finite adeles. -/
theorem complexFiniteChar_eq_one_iff (a : RationalFiniteAdele) :
    complexFiniteChar a = 1 ↔ a ∈ integralFiniteAdeleSubring := by
  refine ⟨fun h ↦ ?_, complexFiniteChar_eq_one_of_mem_integral⟩
  exact (rationalFiniteAdeleFourierChar_eq_one_iff a).mp
    (Circle.coe_injective (by rw [Circle.coe_one]; exact h))

/-! ## The residue map's kernel and surjectivity -/

/-- The residue vanishes exactly on the dilation range. -/
theorem residueOf_eq_zero_iff (m : ℕ) (hm : m ≠ 0) (r : IntegralFiniteAdele) :
    residueOf m hm r = 0 ↔ r ∈ (integralFiniteAdeleNatDilation m).range := by
  constructor
  · intro h
    refine (QuotientAddGroup.eq_zero_iff _).1 ?_
    have hval := congrArg (residueEquivIntegralFiniteAdeleModDilation m hm) h
    rwa [show (residueEquivIntegralFiniteAdeleModDilation m hm) (residueOf m hm r) =
      QuotientAddGroup.mk' _ r from
        (residueEquivIntegralFiniteAdeleModDilation m hm).apply_symm_apply _,
      map_zero] at hval
  · intro h
    show (residueEquivIntegralFiniteAdeleModDilation m hm).symm _ = 0
    rw [show QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range r = 0 from
      (QuotientAddGroup.eq_zero_iff _).2 h]
    exact map_zero _

/-- And every residue is attained. -/
theorem residueOf_surjective (m : ℕ) (hm : m ≠ 0) : Function.Surjective (residueOf m hm) := by
  intro z
  refine ⟨(residueEquivIntegralFiniteAdeleModDilation m hm z).out, ?_⟩
  show (residueEquivIntegralFiniteAdeleModDilation m hm).symm _ = z
  rw [show QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range
      (residueEquivIntegralFiniteAdeleModDilation m hm z).out =
    residueEquivIntegralFiniteAdeleModDilation m hm z from Quotient.out_eq _]
  exact (residueEquivIntegralFiniteAdeleModDilation m hm).symm_apply_apply z

/-! ## Exact conductor -/

/-- The frequency clears nothing smaller than `m`: whenever `t * r` is integral at an integral `r`,
already `r` is an `m`-multiple.  This is the exactness the conductor condition does not supply. -/
def HasExactConductor (t : RationalFiniteAdele) (m : ℕ) : Prop :=
  ∀ r : IntegralFiniteAdele, t * (r : RationalFiniteAdele) ∈ integralFiniteAdeleSubring →
    r ∈ (integralFiniteAdeleNatDilation m).range

/-- Exactness gives injectivity, through the character's exact kernel. -/
theorem injective_residueChar (m : ℕ) (hm : m ≠ 0) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hex : HasExactConductor t m) :
    Function.Injective (residueChar m hm htm) := by
  intro a b hab
  obtain ⟨r, rfl⟩ := residueOf_surjective m hm a
  obtain ⟨s, rfl⟩ := residueOf_surjective m hm b
  rw [residueChar_residueOf, residueChar_residueOf] at hab
  have hne : ∀ a : RationalFiniteAdele, complexFiniteChar a ≠ 0 := fun a ↦ by
    refine left_ne_zero_of_mul_eq_one (b := complexFiniteChar (-a)) ?_
    rw [← AddChar.map_add_eq_mul, add_neg_cancel]
    exact AddChar.map_zero_eq_one _
  have hcoe : ((r - s : IntegralFiniteAdele) : RationalFiniteAdele) =
      (r : RationalFiniteAdele) - (s : RationalFiniteAdele) := AddSubgroup.coe_sub _ _ _
  have hdiff : complexFiniteChar (t * ((r - s : IntegralFiniteAdele) : RationalFiniteAdele)) = 1 := by
    rw [hcoe, mul_sub, AddChar.map_sub_eq_div, hab, div_self (hne _)]
  have hmem := hex (r - s) ((complexFiniteChar_eq_one_iff _).1 hdiff)
  have hzero : residueOf m hm (r - s) = 0 := (residueOf_eq_zero_iff m hm (r - s)).2 hmem
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-! ## The reciprocal frequency -/

/-- The reciprocal frequency `1/m`, as a finite adele. -/
noncomputable def reciprocalFrequency (m : ℕ) : RationalFiniteAdele :=
  algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹)

/-- It clears its own conductor, the product being exactly one. -/
theorem reciprocalFrequency_mul_natCast (m : ℕ) (hm : m ≠ 0) :
    reciprocalFrequency m * (m : RationalFiniteAdele) = 1 := by
  rw [reciprocalFrequency, show (m : RationalFiniteAdele) =
    algebraMap ℚ RationalFiniteAdele (m : ℚ) by simp, ← map_mul,
    inv_mul_cancel₀ (by exact_mod_cast hm)]
  exact map_one _

theorem reciprocalFrequency_conductor (m : ℕ) (hm : m ≠ 0) :
    reciprocalFrequency m * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring := by
  rw [reciprocalFrequency_mul_natCast m hm]
  exact Subring.one_mem _

/-- And it clears nothing smaller: `r = m * ((1/m) * r)` exhibits the multiple. -/
theorem reciprocalFrequency_hasExactConductor (m : ℕ) (hm : m ≠ 0) :
    HasExactConductor (reciprocalFrequency m) m := by
  intro r h
  refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
  show (m : ℕ) • (reciprocalFrequency m * (r : RationalFiniteAdele)) = _
  rw [nsmul_eq_mul, ← mul_assoc, mul_comm (m : RationalFiniteAdele),
    reciprocalFrequency_mul_natCast m hm, one_mul]

/-- SO its residue character is injective, at every conductor. -/
theorem injective_residueChar_reciprocalFrequency (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (residueChar m hm (reciprocalFrequency_conductor m hm)) :=
  injective_residueChar m hm _ (reciprocalFrequency_hasExactConductor m hm)

/-- The frequency is genuinely outside the character's kernel beyond the trivial conductor: `1/m`
is not an integer. -/
theorem reciprocalFrequency_not_mem_integral (m : ℕ) (hm : 2 ≤ m) :
    reciprocalFrequency m ∉ integralFiniteAdeleSubring := by
  intro h
  obtain ⟨z, hz0⟩ := (rational_mem_integralFiniteAdeleSubring_iff ((m : ℚ)⁻¹)).1 h
  have hz : (z : ℚ) = ((m : ℚ))⁻¹ := by simpa using hz0
  have hmpos : (0 : ℚ) < (m : ℚ) := by
    have : (0 : ℕ) < m := lt_of_lt_of_le (by norm_num) hm
    exact_mod_cast this
  have hlt : ((z : ℚ)) < 1 := by
    rw [hz, inv_lt_one_iff₀]
    exact Or.inr (by exact_mod_cast hm)
  have hpos : (0 : ℚ) < (z : ℚ) := by
    rw [hz]
    positivity
  have h1 : z < 1 := by exact_mod_cast hlt
  have h2 : 0 < z := by exact_mod_cast hpos
  omega

/-! ## Summability for the reciprocal frequency -/

/-- The finite-place summability, with no hypothesis left: for the reciprocal frequencies the local
integrals of the frequency phase against the lattice's own form matrix are summable against the
totient multiplicity above rank four. -/
theorem summable_totient_mul_norm_integral_reciprocalPhase (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) :
    Summable (fun m : ℕ ↦ (Nat.totient m : ℝ) *
      ‖if m = 0 then (0 : ℂ) else
        ∫ x, complexFiniteChar
            (scaledQuadratic (reciprocalFrequency m) (integralModelMatrix L.pairingMatrix) x)
          ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖) :=
  summable_totient_mul_norm_integral_scaledPhase L hn reciprocalFrequency
    (fun m hm ↦ reciprocalFrequency_conductor m hm)
    (fun m hm ↦ injective_residueChar_reciprocalFrequency m hm)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
