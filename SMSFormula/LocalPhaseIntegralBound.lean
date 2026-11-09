import SMSFormula.IntegralModelReduction
import SMSFormula.FiniteConductorSummability

/-!
# The local integral of the frequency phase, bounded

Every piece of the finite-place chain is in place, and this file composes them: the local
integral over the integral finite-adelic vectors is `m^(-n)` times a sum of the residue character at
an affine quadratic in the residue vector, and with the integral model that sum obeys the modulus
bound.  The conclusion is the normalized form `‖G_m‖^2 ≤ (m^n)^(-1) |polarDeterminant L|^n` -- exactly the shape
`FiniteConductorSummability` consumes.

The missing link was a round trip, and it costs nothing: the level-quotient identification sends a
class to the residue vector of any of its representatives, because its inverse is the coordinatewise
residue map.  So the summand at the residue vector `w` is the phase at a lift, and the phase step
rewrites that as the residue character at `affineQuadratic` of the reduced matrix -- at `w` itself.

Negative scope.  Injectivity of the residue character remains a hypothesis, carried explicitly
through every statement here.  It is not a formality: the zero frequency satisfies the conductor
condition at every level, its residue character is the trivial one, and the bound then fails -- the
sum is `m^n` and the left side is `1`, against a right side that tends to zero.  Nothing here
evaluates a Gauss sum, and the summability conclusion is conditional on a family of injective
residue characters.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix

variable {n : ℕ}

/-! ## The round trip -/

/-- The identification's inverse is the residue vector: the class of an integral vector is sent back
to that vector's coordinatewise residues, no representative chosen. -/
theorem residueVectorEquivLevelQuotient_symm_mk (m : ℕ) (hm : m ≠ 0)
    (x : Fin n → IntegralFiniteAdele) :
    (residueVectorEquivLevelQuotient n m hm).symm (QuotientAddGroup.mk x) =
      residueVector m hm x := by
  funext i
  simp only [residueVectorEquivLevelQuotient, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
    AddEquiv.piCongrRight_symm, AddEquiv.piCongrRight_apply]
  rfl

/-- Hence the summand at a residue vector is the residue character at the affine quadratic in that
very vector -- the phase step's identity, transported through the index identification. -/
theorem phaseQuotient_residueVectorEquiv (m : ℕ) (hm : m ≠ 0)
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (w : Fin n → ZMod m) :
    phaseQuotient (scaledQuadratic_polarization t C) complexFiniteChar
        (level_of_conductor m hC htm) (residueVectorEquivLevelQuotient n m hm w) =
      residueChar m hm htm (affineQuadratic (reducedMatrix m hm C hC) 0 0 w) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective
    (residueVectorEquivLevelQuotient n m hm w)
  have hres : residueVector m hm x = w := by
    rw [← residueVectorEquivLevelQuotient_symm_mk m hm x, hx, AddEquiv.symm_apply_apply]
  rw [← hx, phaseQuotient_mk]
  rw [show scaledQuadratic t C x = t * adelicQuadratic C x from rfl,
    complexFiniteChar_scaledQuadratic_eq_residueChar m hm hC htm x, hres]

/-! ## The local integral as a normalized character sum -/

/-- The local integral is `m^(-n)` times the character sum the modulus bound is stated over. -/
theorem integral_scaledPhase_eq_residueChar_sum (m : ℕ) [NeZero m]
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∫ x, complexFiniteChar (scaledQuadratic t C x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ((m ^ n : ℝ))⁻¹ • ∑ w : Fin n → ZMod m,
        residueChar m (NeZero.ne m) htm
          (affineQuadratic (reducedMatrix m (NeZero.ne m) C hC) 0 0 w) := by
  rw [integral_scaledPhase_eq_residueVector_sum m hC htm]
  congr 1
  exact Finset.sum_congr rfl fun w _ ↦
    phaseQuotient_residueVectorEquiv m (NeZero.ne m) hC htm w

/-! ## The bound -/

/-- The normalized bound on the local integral, for the lattice's own form matrix: the squared
modulus is at most `(m^n)^(-1) |polarDeterminant L|^n`, the conductor going into the denominator.  Injectivity
of the residue character is the one remaining hypothesis. -/
theorem norm_sq_integral_scaledPhase_le (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m (NeZero.ne m) htm)) :
    ‖∫ x, complexFiniteChar (scaledQuadratic t (integralModelMatrix L.pairingMatrix) x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ ^ 2 ≤
      (((m : ℝ)) ^ n)⁻¹ * ((L.polarDeterminant.natAbs : ℝ)) ^ n := by
  have hm : m ≠ 0 := NeZero.ne m
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [integral_scaledPhase_eq_residueChar_sum m (integralModelMatrix_mem L.pairingMatrix) htm]
  have hsum := norm_sq_sum_char_lattice_le L m hm hinj (0 : Fin n → ZMod m) (0 : ZMod m)
  have hne : ((m : ℝ) ^ n) ≠ 0 := by positivity
  rw [norm_smul, mul_pow]
  have hnormsmul : ‖((m ^ n : ℝ))⁻¹‖ ^ 2 = (((m : ℝ) ^ n)⁻¹) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnormsmul]
  have hstep : (((m : ℝ) ^ n)⁻¹) ^ 2 *
      ‖∑ w : Fin n → ZMod m, residueChar m hm htm
        (affineQuadratic (reducedMatrix m hm (integralModelMatrix L.pairingMatrix)
          (integralModelMatrix_mem L.pairingMatrix)) 0 0 w)‖ ^ 2 ≤
      (((m : ℝ) ^ n)⁻¹) ^ 2 * ((m : ℝ) ^ n * ((L.polarDeterminant.natAbs : ℝ)) ^ n) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-! ## The composition check -/

/-- The composition, checked rather than asserted: a family of frequencies, one per conductor, each
clearing its conductor and with injective residue character, makes the local integrals summable
against the totient multiplicity above rank four. -/
theorem summable_totient_mul_norm_integral_scaledPhase (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    (t : ℕ → RationalFiniteAdele)
    (htm : ∀ m : ℕ, m ≠ 0 →
      t m * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : ∀ m : ℕ, ∀ hm : m ≠ 0,
      Function.Injective (residueChar m hm (htm m hm))) :
    Summable (fun m : ℕ ↦ (Nat.totient m : ℝ) *
      ‖if m = 0 then (0 : ℂ) else
        ∫ x, complexFiniteChar (scaledQuadratic (t m) (integralModelMatrix L.pairingMatrix) x)
          ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖) := by
  refine summable_totient_mul_norm_of_det_bound hn L.polarDeterminant.natAbs _ ?_
  intro m hm
  rw [if_neg hm]
  haveI : NeZero m := ⟨hm⟩
  have := norm_sq_integral_scaledPhase_le L m (htm m hm) (hinj m hm)
  convert this using 3

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
