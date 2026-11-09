import SMSFormula.ResidueCharacterInjectivity

/-!
# Every primitive fraction has exact conductor, and the coefficient is periodic

The conductor-indexed summability (`FiniteConductorSummability`) runs along one frequency per
conductor.  Identifying that sum with the finite-adelic `L^1` integral of the adelic Bruhat
coefficient needs two arithmetic inputs before any measure theory, and this file supplies both.

First, exactness at every primitive fraction.  `a/m` with `a` coprime to `m` has exact conductor
`m`, by Bezout and nothing else: from `u a + v m = 1`, if `(a/m) r` is integral then
`r/m = u (a r/m) + v r` is a sum of integral terms, so `r` is an `m`-multiple.  The reciprocal is
the case `a = 1`, recovered.  This is where the totient multiplicity comes from: the admissible
frequencies of conductor `m` are indexed by the units mod `m`, not by a single representative.

Second, periodicity.  The local integral is unchanged by an integral shift of the frequency, and
pointwise so -- `psi((t+u) Q x) = psi(t Q x) psi(u Q x)` and the second factor is `1` because `u`
and `Q x` are both integral.  No measure theory is used at all.  This is the fact that makes the
finite-adelic integral a sum over `A_f / Zhat`, each class contributing its own constant value.

Negative scope.  The measure-theoretic half is not here: nothing computes the mass of a conductor
stratum, nothing decomposes the finite adeles as the union of the `m^(-1) Zhat`, and nothing
identifies this local integral with the finite factor of the repository's adelic Bruhat coefficient.
The stratum mass and the identification are `ConductorStratumMass` and
`FiniteFactorIdentification`.  No Gauss sum is evaluated.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix

variable {n : ℕ}

/-! ## The primitive fractions -/

/-- The frequency `a/m`. -/
noncomputable def primitiveFrequency (a : ℤ) (m : ℕ) : RationalFiniteAdele :=
  algebraMap ℚ RationalFiniteAdele ((a : ℚ) / (m : ℚ))

/-- Clearing the conductor returns the numerator. -/
theorem natCast_mul_primitiveFrequency (a : ℤ) (m : ℕ) (hm : m ≠ 0) :
    (m : RationalFiniteAdele) * primitiveFrequency a m =
      algebraMap ℤ RationalFiniteAdele a := by
  rw [primitiveFrequency, show (m : RationalFiniteAdele) =
    algebraMap ℚ RationalFiniteAdele (m : ℚ) by simp, ← map_mul,
    mul_div_cancel₀ _ (by exact_mod_cast hm : ((m : ℚ)) ≠ 0)]
  simp

/-- SO it clears its conductor, the numerator being an integer. -/
theorem primitiveFrequency_conductor (a : ℤ) (m : ℕ) (hm : m ≠ 0) :
    primitiveFrequency a m * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring := by
  rw [mul_comm, natCast_mul_primitiveFrequency a m hm]
  exact algebraMap_int_mem_integralFiniteAdeleSubring a

/-- And at a coprime numerator it clears nothing smaller -- Bezout, and nothing else. -/
theorem primitiveFrequency_hasExactConductor (a : ℤ) (m : ℕ) (hm : m ≠ 0)
    (hcop : IsCoprime a (m : ℤ)) :
    HasExactConductor (primitiveFrequency a m) m := by
  obtain ⟨u, v, huv⟩ := hcop
  intro r hr
  refine ⟨⟨(algebraMap ℤ RationalFiniteAdele u) * (primitiveFrequency a m *
      (r : RationalFiniteAdele)) +
      (algebraMap ℤ RationalFiniteAdele v) * (r : RationalFiniteAdele), ?_⟩, Subtype.ext ?_⟩
  · exact Subring.add_mem _
      (Subring.mul_mem _ (algebraMap_int_mem_integralFiniteAdeleSubring u) hr)
      (Subring.mul_mem _ (algebraMap_int_mem_integralFiniteAdeleSubring v) r.property)
  · have hone : (algebraMap ℤ RationalFiniteAdele u) * (algebraMap ℤ RationalFiniteAdele a) +
        (m : RationalFiniteAdele) * (algebraMap ℤ RationalFiniteAdele v) = 1 := by
      have hmap := congrArg (algebraMap ℤ RationalFiniteAdele) huv
      rw [map_add, map_mul, map_mul, map_one] at hmap
      rw [show algebraMap ℤ RationalFiniteAdele ((m : ℤ)) =
        (m : RationalFiniteAdele) by simp] at hmap
      linear_combination hmap
    have hclear := natCast_mul_primitiveFrequency a m hm
    show (m : ℕ) • _ = _
    rw [nsmul_eq_mul]
    linear_combination (algebraMap ℤ RationalFiniteAdele u * (r : RationalFiniteAdele)) * hclear +
      (r : RationalFiniteAdele) * hone

/-- Hence its residue character is injective. -/
theorem injective_residueChar_primitiveFrequency (a : ℤ) (m : ℕ) (hm : m ≠ 0)
    (hcop : IsCoprime a (m : ℤ)) :
    Function.Injective (residueChar m hm (primitiveFrequency_conductor a m hm)) :=
  injective_residueChar m hm _ (primitiveFrequency_hasExactConductor a m hm hcop)

/-- The reciprocal is the case `a = 1`, recovered. -/
theorem reciprocalFrequency_eq_primitiveFrequency (m : ℕ) :
    reciprocalFrequency m = primitiveFrequency 1 m := by
  rw [reciprocalFrequency, primitiveFrequency]
  norm_num

/-! ## The bound at every primitive frequency -/

/-- The normalized bound holds at every primitive fraction, not just the reciprocal -- which is
what the totient multiplicity needs. -/
theorem norm_sq_integral_primitivePhase_le (L : PositiveDefiniteIntegralLattice n) (a : ℤ) (m : ℕ) [NeZero m]
    (hcop : IsCoprime a (m : ℤ)) :
    ‖∫ x, complexFiniteChar
        (scaledQuadratic (primitiveFrequency a m) (integralModelMatrix L.pairingMatrix) x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ ^ 2 ≤
      (((m : ℝ)) ^ n)⁻¹ * ((L.polarDeterminant.natAbs : ℝ)) ^ n :=
  norm_sq_integral_scaledPhase_le L m (primitiveFrequency_conductor a m (NeZero.ne m))
    (injective_residueChar_primitiveFrequency a m (NeZero.ne m) hcop)

/-! ## Periodicity in the frequency -/

/-- The phase is unchanged by an integral shift of the frequency, pointwise: the extra factor is
`psi (u Q x)` with `u` and `Q x` both integral, hence one. -/
theorem complexFiniteChar_scaledQuadratic_add_integral
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) (t u : RationalFiniteAdele)
    (hu : u ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele) :
    complexFiniteChar (scaledQuadratic (t + u) C x) =
      complexFiniteChar (scaledQuadratic t C x) := by
  show complexFiniteChar ((t + u) * adelicQuadratic C x) = _
  rw [add_mul, AddChar.map_add_eq_mul,
    complexFiniteChar_eq_one_of_mem_integral
      (Subring.mul_mem _ hu (adelicQuadratic_mem_integral hC x)), mul_one]
  rfl

/-- SO the local integral is a function of the frequency's class modulo the integral finite adeles
-- the fact that turns the finite-adelic integral into a sum over `A_f / Zhat`.  No measure theory
is used: the integrands are equal. -/
theorem integral_scaledPhase_add_integral
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) (t u : RationalFiniteAdele)
    (hu : u ∈ integralFiniteAdeleSubring) :
    ∫ x, complexFiniteChar (scaledQuadratic (t + u) C x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ∫ x, complexFiniteChar (scaledQuadratic t C x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  exact complexFiniteChar_scaledQuadratic_add_integral hC t u hu x

/-! ## The classes are indexed by the residues -/

/-- The difference of two primitive fractions at the same conductor is one of them. -/
theorem primitiveFrequency_sub (a b : ℤ) (m : ℕ) :
    primitiveFrequency a m - primitiveFrequency b m = primitiveFrequency (a - b) m := by
  rw [primitiveFrequency, primitiveFrequency, primitiveFrequency, ← map_sub]
  congr 1
  push_cast
  ring

/-- And it is integral exactly when the conductor divides the numerator. -/
theorem primitiveFrequency_mem_integral_iff (a : ℤ) (m : ℕ) (hm : m ≠ 0) :
    primitiveFrequency a m ∈ integralFiniteAdeleSubring ↔ (m : ℤ) ∣ a := by
  have hmq : ((m : ℚ)) ≠ 0 := by exact_mod_cast hm
  rw [primitiveFrequency, rational_mem_integralFiniteAdeleSubring_iff]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : (z : ℚ) = (a : ℚ) / (m : ℚ) := by simpa using hz
    refine ⟨z, ?_⟩
    have hmul : (m : ℚ) * (z : ℚ) = (a : ℚ) := by rw [hz']; field_simp
    exact_mod_cast hmul.symm
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    show ((z : ℚ)) = _
    push_cast
    field_simp

/-- Hence two primitive fractions Lie in the same class modulo the integral finite adeles exactly
when their numerators agree in `ZMod m` -- so, with periodicity, the local integral is a function
of the residue of the numerator, and the admissible conductor-`m` frequencies are indexed by the
units of `ZMod m`, of which there are `phi(m)`. -/
theorem primitiveFrequency_sub_mem_integral_iff (a b : ℤ) (m : ℕ) (hm : m ≠ 0) :
    primitiveFrequency a m - primitiveFrequency b m ∈ integralFiniteAdeleSubring ↔
      (a : ZMod m) = (b : ZMod m) := by
  rw [primitiveFrequency_sub, primitiveFrequency_mem_integral_iff _ m hm,
    ZMod.intCast_eq_intCast_iff]
  exact ⟨fun h ↦ (Int.modEq_iff_dvd.mpr h).symm, fun h ↦ Int.modEq_iff_dvd.mp h.symm⟩

/-! ## The summability, over an arbitrary choice of primitive numerators -/

/-- The summability with the numerators free: any choice of a coprime numerator at each conductor
gives a summable family above rank four.  The reciprocal family is the constant choice `1`. -/
theorem summable_totient_mul_norm_integral_primitivePhase (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    (a : ℕ → ℤ) (hcop : ∀ m : ℕ, m ≠ 0 → IsCoprime (a m) (m : ℤ)) :
    Summable (fun m : ℕ ↦ (Nat.totient m : ℝ) *
      ‖if m = 0 then (0 : ℂ) else
        ∫ x, complexFiniteChar
            (scaledQuadratic (primitiveFrequency (a m) m) (integralModelMatrix L.pairingMatrix) x)
          ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖) :=
  summable_totient_mul_norm_integral_scaledPhase L hn (fun m ↦ primitiveFrequency (a m) m)
    (fun m hm ↦ primitiveFrequency_conductor (a m) m hm)
    (fun m hm ↦ injective_residueChar_primitiveFrequency (a m) m hm (hcop m hm))

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
