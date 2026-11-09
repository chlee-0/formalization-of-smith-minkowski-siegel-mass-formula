import SMSFormula.QuadraticPhaseDescent
import SMSFormula.RationalFiniteAdeleIntegralLatticeFiniteQuotient

/-!
# The descent on the repository's own integral finite-adelic vectors

`QuadraticPhaseDescent` descends a quadratic phase to the quotient by a level subgroup, with the
subgroup, its finite quotient and the character's level all hypotheses.  This file discharges all
three on the repository's own objects, so the local integral of a quadratic phase over the integral
finite-adelic vectors becomes an explicitly normalized finite sum.

A correction to our own record, worth stating plainly: the collapse proved in `CosetAverageIntegral`
was already repository state as `integral_comp_quotientAddGroupMk_eq_measure_mul_sum`, in the very
file this one imports.  The locate-first note should have caught that and did not.  What that file
genuinely adds is the identification of the common fiber mass with `1/card` at a probability measure,
and the normalized and norm forms; the collapse itself is used here from the repository's lemma, not
ours.

What is discharged here.  The level subgroup is the repository's own `m`-dilation range, whose members
are visibly `m` times an element, so the scale criterion applies with no new construction.  Its
quotient is finite with index exactly `m ^ n`, and its carrier is measurable -- both repository
theorems.  The coordinate Haar measure is already a left-invariant probability measure.  So the only
surviving hypothesis is the character's level: that it kills `m`-multiples.

The polarization is supplied concretely for the dot-product form of a matrix, which is the shape the
repository's quadratic forms actually have -- pure algebra over a commutative ring, no analysis.

Negative scope.  The character's level is still a hypothesis: no conductor is computed and no
character is constructed.  Nothing is evaluated -- the normalization `m ^ (-n)` is exactly what the
conductor bounds are stated against, and all the decay still has to come from the sum.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent Matrix

/-! ## The level subgroup is the repository's own dilation range -/

/-- The level subgroup at level `m`: the repository's own coordinate dilation range. -/
noncomputable abbrev levelSubgroup (n m : ℕ) : AddSubgroup (Fin n → IntegralFiniteAdele) :=
  (integralFiniteAdeleCoordinateNatDilation n m).range

/-- The dilation is literally the scaling, so every member of the level subgroup is `m` times an
element -- the scale criterion's hypothesis, discharged with no construction. -/
theorem exists_nsmul_of_mem_levelSubgroup (n m : ℕ) (h : Fin n → IntegralFiniteAdele)
    (hh : h ∈ levelSubgroup n m) : ∃ u : Fin n → IntegralFiniteAdele, h = m • u := by
  obtain ⟨u, rfl⟩ := hh
  refine ⟨u, ?_⟩
  funext i
  apply Subtype.ext
  rfl

/-- The fibers of the level quotient are measurable, from the repository's own measurability of the
dilation range. -/
theorem measurableSet_preimage_mk_levelSubgroup (n m : ℕ) (hm : m ≠ 0)
    (q : (Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m) :
    MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set (Fin n → IntegralFiniteAdele)) :=
  SMSFormula.CosetAverage.measurableSet_preimage_mk
    (measurableSet_integralFiniteAdeleCoordinateNatDilation_range n m hm) q

/-- The quotient has exactly `m ^ n` classes, from the repository's own index computation. -/
theorem card_quotient_levelSubgroup (n m : ℕ) [NeZero m] :
    Fintype.card ((Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m) = m ^ n := by
  rw [← Nat.card_eq_fintype_card]
  exact integralFiniteAdeleCoordinateNatDilation_range_index n m (NeZero.ne m)

/-! ## The polarization of a dot-product quadratic form -/

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The quadratic form of a matrix, in the shape the repository's forms actually have. -/
def dotQuadratic (C : Matrix (Fin n) (Fin n) R) (x : Fin n → R) : R := x ⬝ᵥ (C *ᵥ x)

/-- Its polarization. -/
def dotPolar (C : Matrix (Fin n) (Fin n) R) (x h : Fin n → R) : R :=
  x ⬝ᵥ (C *ᵥ h) + h ⬝ᵥ (C *ᵥ x)

/-- The polarization identity, pure algebra over a commutative ring. -/
theorem dotQuadratic_polarization (C : Matrix (Fin n) (Fin n) R) (x h : Fin n → R) :
    dotQuadratic C (x + h) = dotQuadratic C x + dotPolar C x h + dotQuadratic C h := by
  simp only [dotQuadratic, dotPolar, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

/-! ## Transporting it to the integral vectors

`IntegralFiniteAdele` is an additive subgroup, not a ring, so the form's values do not live in the
same type as the vectors.  The coordinates are pushed into the ambient finite adeles, where the ring
structure is, and the polarization transports because that push is additive. -/

/-- The coordinates of an integral vector, in the ambient finite adeles. -/
def coordCoe {n : ℕ} (x : Fin n → IntegralFiniteAdele) : Fin n → RationalFiniteAdele :=
  fun i ↦ (x i : RationalFiniteAdele)

theorem coordCoe_add {n : ℕ} (x h : Fin n → IntegralFiniteAdele) :
    coordCoe (x + h) = coordCoe x + coordCoe h := rfl

/-- The form on integral vectors, with values in the ambient finite adeles. -/
noncomputable def adelicQuadratic {n : ℕ} (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (x : Fin n → IntegralFiniteAdele) : RationalFiniteAdele := dotQuadratic C (coordCoe x)

/-- And its polarization. -/
noncomputable def adelicPolar {n : ℕ} (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (x h : Fin n → IntegralFiniteAdele) : RationalFiniteAdele :=
  dotPolar C (coordCoe x) (coordCoe h)

theorem adelicQuadratic_polarization {n : ℕ} (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (x h : Fin n → IntegralFiniteAdele) :
    adelicQuadratic C (x + h) = adelicQuadratic C x + adelicPolar C x h + adelicQuadratic C h := by
  simp only [adelicQuadratic, adelicPolar, coordCoe_add]
  exact dotQuadratic_polarization C (coordCoe x) (coordCoe h)

/-! ## The payoff on the repository's own objects -/

/-- The local integral of a quadratic phase over the integral finite-adelic vectors is the
normalized finite sum over the repository's own level-`m` quotient, the normalization being exactly
`m ^ (-n)` -- the shape the conductor bounds are stated against.  The level subgroup, its finite
quotient, the fiber measurability and the invariant probability measure are all the repository's
own; the only surviving hypothesis is the character's level. -/
theorem integral_adelicQuadratic_phase_eq_normalized_sum (n m : ℕ) [NeZero m]
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (psi : AddChar RationalFiniteAdele ℂ)
    (hlevel : ∀ x : Fin n → IntegralFiniteAdele, ∀ h ∈ levelSubgroup n m,
      psi (adelicPolar C x h + adelicQuadratic C h) = 1) :
    ∫ x, psi (adelicQuadratic C x) ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ((m ^ n : ℝ))⁻¹ • ∑ q : (Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m,
        phaseQuotient (adelicQuadratic_polarization C) psi hlevel q := by
  have hfib := measurableSet_preimage_mk_levelSubgroup n m (NeZero.ne m)
  rw [SMSFormula.QuadraticPhaseDescent.integral_phase_eq_average
    (integralFiniteAdeleCoordinateAddHaarMeasure n) (adelicQuadratic_polarization C) psi hlevel
    hfib, card_quotient_levelSubgroup n m]
  norm_cast

/-- And the level hypothesis reduces to the character, by the scale criterion: the level subgroup's
members are `m` times an element, and the form's polarization and square law are `m`-homogeneous in
the required slots.  The character hypothesis is stated over the whole ambient ring here; the
restricted form, over the values actually occurring, is what a conductor would supply. -/
theorem level_of_character_kills (n m : ℕ)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (psi : AddChar RationalFiniteAdele ℂ)
    (hkill : ∀ r : RationalFiniteAdele, psi (m • r) = 1) :
    ∀ x : Fin n → IntegralFiniteAdele, ∀ h ∈ levelSubgroup n m,
      psi (adelicPolar C x h + adelicQuadratic C h) = 1 := by
  refine level_of_natScale psi m ?_ ?_ hkill (exists_nsmul_of_mem_levelSubgroup n m)
  · intro x u
    have hc : coordCoe (m • u) = m • coordCoe u := rfl
    simp only [adelicPolar, dotPolar, hc, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_add]
  · intro u
    have hc : coordCoe (m • u) = m • coordCoe u := rfl
    simp only [adelicQuadratic, dotQuadratic, hc, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
