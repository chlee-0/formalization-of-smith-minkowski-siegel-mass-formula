import SMSFormula.ConductorFiltration

/-!
# Every frequency has an exact conductor, and the stratum is the primitive fractions

The conductor filtration does not by itself give a frequency an exact conductor, and a mass
computation for the exact-conductor stratum needs the stratum described, not merely defined.  Both
follow from one reduction.

Exactness is a class invariant: an integral translation of the frequency changes `t r` by the
integral `u r`, so it changes neither the conductor condition nor exactness.  Nothing else about the
translation is used.

Every cleared frequency is a primitive fraction modulo the integers: writing `t = (1/m) s` with `s`
integral and reducing `s` to an integer modulo `m` -- the repository's own `exists_int_congrMod` --
gives `t - z/m` integral.  So the class of `t` modulo `Zhat` is the class of an actual fraction.

Hence every frequency has an exact conductor: cancel the gcd.  `z/m = z'/m'` with `z'` coprime to
`m'`, the coprime fraction has exact conductor `m'` by Bezout, and exactness transfers back along
the integral translation.  Combined with uniqueness the exact conductor is a genuine invariant
of the frequency, existing and unique.

And the stratum is exactly the primitive fractions: `t` has exact conductor `m` iff `t` is congruent
modulo `Zhat` to `a/m` with `a` coprime to `m`.  With the class indexing already in hand, those
classes are the units of `ZMod m`, which mathlib counts as `phi(m)` -- so the index set of the
stratum is identified, which is what a mass computation needs.

Negative scope.  Still no measure: nothing evaluates the mass of a class or of a stratum, and
nothing identifies the local integral with the finite factor of the adelic Bruhat coefficient.  The
identification here is of index sets.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent Matrix

/-! ## Exactness is a class invariant -/

/-- Clearing is unchanged by an integral translation of the frequency. -/
theorem mul_mem_integral_congr {t t' : RationalFiniteAdele}
    (h : t - t' ∈ integralFiniteAdeleSubring) {r : RationalFiniteAdele}
    (hr : r ∈ integralFiniteAdeleSubring) :
    t * r ∈ integralFiniteAdeleSubring ↔ t' * r ∈ integralFiniteAdeleSubring := by
  have hdiff : t * r - t' * r ∈ integralFiniteAdeleSubring := by
    rw [show t * r - t' * r = (t - t') * r from by ring]
    exact Subring.mul_mem _ h hr
  constructor
  · intro ht
    have : t * r - (t * r - t' * r) ∈ integralFiniteAdeleSubring := Subring.sub_mem _ ht hdiff
    simpa using this
  · intro ht
    have : t' * r + (t * r - t' * r) ∈ integralFiniteAdeleSubring := Subring.add_mem _ ht hdiff
    simpa using this

/-- SO is the conductor condition. -/
theorem mul_natCast_mem_integral_congr {t t' : RationalFiniteAdele}
    (h : t - t' ∈ integralFiniteAdeleSubring) (m : ℕ) :
    t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ↔
      t' * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring :=
  mul_mem_integral_congr h (natCast_mem _ m)

/-- And SO is exactness. -/
theorem hasExactConductor_congr {t t' : RationalFiniteAdele}
    (h : t - t' ∈ integralFiniteAdeleSubring) (m : ℕ) :
    HasExactConductor t m ↔ HasExactConductor t' m := by
  constructor
  · intro hex r hr
    exact hex r ((mul_mem_integral_congr h r.property).2 hr)
  · intro hex r hr
    exact hex r ((mul_mem_integral_congr h r.property).1 hr)

/-! ## Every cleared frequency is a primitive fraction modulo the integers -/

/-- The primitive fraction is the reciprocal times the numerator. -/
theorem reciprocalFrequency_mul_intCast (z : ℤ) (m : ℕ) :
    reciprocalFrequency m * algebraMap ℤ RationalFiniteAdele z = primitiveFrequency z m := by
  rw [reciprocalFrequency, primitiveFrequency,
    show algebraMap ℤ RationalFiniteAdele z = algebraMap ℚ RationalFiniteAdele (z : ℚ) by simp,
    ← map_mul]
  congr 1
  field_simp

/-- Every frequency clearing `m` is congruent modulo the integral finite adeles to an actual
fraction with denominator `m` -- the repository's own integer reduction, divided by `m`. -/
theorem exists_primitiveFrequency_congr {t : RationalFiniteAdele} {m : ℕ} (hm : m ≠ 0)
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∃ z : ℤ, t - primitiveFrequency z m ∈ integralFiniteAdeleSubring := by
  obtain ⟨s, hs, rfl⟩ := (mul_natCast_mem_integral_iff t m hm).1 htm
  obtain ⟨z, ⟨u, hu, huval⟩, -⟩ := exists_int_congrMod (m := m) hm ⟨s, hs⟩
  refine ⟨z, ?_⟩
  have hval : s - algebraMap ℤ RationalFiniteAdele z = (m : RationalFiniteAdele) * u := by
    rw [algebraMap_int_eq_coe_integerToIntegralFiniteAdele z]
    exact huval
  have hrewrite : reciprocalFrequency m * s - primitiveFrequency z m = u := by
    have hmul : reciprocalFrequency m * (m : RationalFiniteAdele) = 1 :=
      reciprocalFrequency_mul_natCast m hm
    rw [← reciprocalFrequency_mul_intCast z m, ← mul_sub, hval]
    linear_combination u * hmul
  rw [hrewrite]
  exact hu

/-! ## Cancelling the gcd -/

/-- Cancelling the GCD does not move the fraction. -/
theorem primitiveFrequency_div_gcd (z : ℤ) (m : ℕ) (hm : m ≠ 0) :
    primitiveFrequency z m =
      primitiveFrequency (z / (Int.gcd z (m : ℤ) : ℤ)) (m / Int.gcd z (m : ℤ)) := by
  set d : ℕ := Int.gcd z (m : ℤ) with hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [hd, Int.gcd_eq_zero_iff] at h
    exact hm (by exact_mod_cast h.2)
  have hdz : (d : ℤ) ∣ z := hd ▸ Int.gcd_dvd_left z (m : ℤ)
  have hdm : d ∣ m := by
    have h : (d : ℤ) ∣ (m : ℤ) := hd ▸ Int.gcd_dvd_right z (m : ℤ)
    exact_mod_cast h
  have hdq : ((d : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hmq : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [primitiveFrequency, primitiveFrequency]
  congr 1
  rw [Int.cast_div_charZero hdz, Nat.cast_div hdm hdq]
  push_cast
  field_simp

/-- And the reduced numerator is coprime to the reduced denominator. -/
theorem isCoprime_div_gcd (z : ℤ) (m : ℕ) (hm : m ≠ 0) :
    IsCoprime (z / (Int.gcd z (m : ℤ) : ℤ)) ((m / Int.gcd z (m : ℤ) : ℕ) : ℤ) := by
  set d : ℕ := Int.gcd z (m : ℤ) with hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [hd, Int.gcd_eq_zero_iff] at h
    exact hm (by exact_mod_cast h.2)
  have hdz : (d : ℤ) ∣ z := hd ▸ Int.gcd_dvd_left z (m : ℤ)
  have hgcd : Nat.gcd z.natAbs m = d := by simp [hd, Int.gcd]
  rw [Int.isCoprime_iff_gcd_eq_one,
    show Int.gcd (z / (d : ℤ)) (((m / d : ℕ)) : ℤ) =
      Nat.gcd (z / (d : ℤ)).natAbs ((((m / d : ℕ)) : ℤ)).natAbs from rfl]
  have hnum : (z / (d : ℤ)).natAbs = z.natAbs / d := by
    rw [Int.natAbs_ediv_of_dvd hdz]
    simp
  have hden : ((((m / d : ℕ)) : ℤ)).natAbs = m / d := Int.natAbs_natCast _
  rw [hnum, hden, ← hgcd]
  exact Nat.coprime_div_gcd_div_gcd (by rw [hgcd]; exact Nat.pos_of_ne_zero hd0)

/-! ## Existence -/

/-- Every frequency has an exact conductor -- the gap the filtration left open.  With uniqueness the
exact conductor is a genuine invariant of the frequency. -/
theorem exists_hasExactConductor (t : RationalFiniteAdele) :
    ∃ m : ℕ, m ≠ 0 ∧ t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧
      HasExactConductor t m := by
  obtain ⟨m, hm, htm⟩ := exists_conductor t
  obtain ⟨z, hz⟩ := exists_primitiveFrequency_congr hm htm
  set d : ℕ := Int.gcd z (m : ℤ) with hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [hd, Int.gcd_eq_zero_iff] at h
    exact hm (by exact_mod_cast h.2)
  have hdm : d ∣ m := by
    have h : (d : ℤ) ∣ (m : ℤ) := hd ▸ Int.gcd_dvd_right z (m : ℤ)
    exact_mod_cast h
  have hm' : m / d ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hd0, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm⟩
  have hcongr : t - primitiveFrequency (z / (d : ℤ)) (m / d) ∈ integralFiniteAdeleSubring := by
    rwa [← primitiveFrequency_div_gcd z m hm]
  refine ⟨m / d, hm', ?_, ?_⟩
  · exact (mul_natCast_mem_integral_congr hcongr (m / d)).2
      (primitiveFrequency_conductor _ (m / d) hm')
  · exact (hasExactConductor_congr hcongr (m / d)).2
      (primitiveFrequency_hasExactConductor _ (m / d) hm' (isCoprime_div_gcd z m hm))

/-! ## The stratum is exactly the primitive fractions -/

/-- The exact-conductor-`m` stratum is exactly the primitive fractions modulo the integral finite
adeles: `t` clears `m` exactly iff it is congruent to `a/m` with `a` coprime to `m`.  With the class
indexing this identifies the stratum's index set with the units of `ZMod m`. -/
theorem hasExactConductor_iff_congr_primitiveFrequency (t : RationalFiniteAdele) (m : ℕ)
    (hm : m ≠ 0) :
    (t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧ HasExactConductor t m) ↔
      ∃ a : ℤ, IsCoprime a (m : ℤ) ∧
        t - primitiveFrequency a m ∈ integralFiniteAdeleSubring := by
  constructor
  · rintro ⟨htm, hex⟩
    obtain ⟨z, hz⟩ := exists_primitiveFrequency_congr hm htm
    set d : ℕ := Int.gcd z (m : ℤ) with hd
    have hd0 : d ≠ 0 := by
      intro h
      rw [hd, Int.gcd_eq_zero_iff] at h
      exact hm (by exact_mod_cast h.2)
    have hdm : d ∣ m := by
      have h : (d : ℤ) ∣ (m : ℤ) := hd ▸ Int.gcd_dvd_right z (m : ℤ)
      exact_mod_cast h
    have hm' : m / d ≠ 0 :=
      Nat.div_ne_zero_iff.mpr ⟨hd0, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm⟩
    have hcongr : t - primitiveFrequency (z / (d : ℤ)) (m / d) ∈ integralFiniteAdeleSubring := by
      rwa [← primitiveFrequency_div_gcd z m hm]
    have hexred : HasExactConductor t (m / d) :=
      (hasExactConductor_congr hcongr (m / d)).2
        (primitiveFrequency_hasExactConductor _ (m / d) hm' (isCoprime_div_gcd z m hm))
    have hcred : t * ((m / d : ℕ) : RationalFiniteAdele) ∈ integralFiniteAdeleSubring :=
      (mul_natCast_mem_integral_congr hcongr (m / d)).2
        (primitiveFrequency_conductor _ (m / d) hm')
    have hdeq : m / d = m := hasExactConductor_unique hm' hm hexred hex hcred htm
    refine ⟨z / (d : ℤ), ?_, ?_⟩
    · have := isCoprime_div_gcd z m hm
      rwa [hdeq] at this
    · rwa [hdeq] at hcongr
  · rintro ⟨a, hcop, hcongr⟩
    exact ⟨(mul_natCast_mem_integral_congr hcongr m).2 (primitiveFrequency_conductor a m hm),
      (hasExactConductor_congr hcongr m).2 (primitiveFrequency_hasExactConductor a m hm hcop)⟩

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
