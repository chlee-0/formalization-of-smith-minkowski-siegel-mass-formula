import SMSFormula.IntegralFiniteAdelePhaseLevel
import SMSFormula.RationalFiniteAdeleAdditiveCharacter
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The conductor: the level condition on the repository's own character

`IntegralFiniteAdelePhaseLevel` left exactly one hypothesis: the character's level.  Its decisive
negative showed why it could not be the global form -- `m` is a unit in the finite adeles, so a
character killing every `m`-multiple is trivial.  This file supplies the restricted form on the
repository's own character, which is what a conductor actually is.

The character is already there, and its kernel is exact.  The repository's
`rationalFiniteAdeleFourierChar` is trivial on the everywhere-integral finite adeles and, by its
own `eq_one_iff`, on nothing else.  Complexifying it changes nothing.

The conductor condition is `t * m` integral, and that is all.  With the form's matrix integral, the
polarization discrepancy at a level-`m` shift is `m` times something integral, so the frequency
phase's discrepancy is `(t * m)` times something integral -- integral exactly when `t * m` is, and
the character kills it.  So the local integral of `psi (t * Q x)` over the integral finite-adelic
vectors is `m ^ (-n)` times the finite sum, with no hypothesis on the character left.

Negative scope.  The conductor condition is a real restriction, not a formality: the character is
not trivial, so the level condition genuinely constrains `t` and `m` together.  No Gauss sum is
evaluated and no decay is produced -- all of that still lives in the finite sum.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent Matrix

/-! ## The repository's character, complexified -/

/-- The finite Fourier character with complex values.  Only the coercion changes. -/
noncomputable def complexFiniteChar : AddChar RationalFiniteAdele ℂ where
  toFun a := (rationalFiniteAdeleFourierChar a : ℂ)
  map_zero_eq_one' := by
    rw [AddChar.map_zero_eq_one]
    exact Circle.coe_one
  map_add_eq_mul' x y := by
    rw [AddChar.map_add_eq_mul]
    exact Circle.coe_mul _ _

@[simp]
theorem complexFiniteChar_apply (a : RationalFiniteAdele) :
    complexFiniteChar a = (rationalFiniteAdeleFourierChar a : ℂ) := rfl

/-- It is trivial exactly on the integral finite adeles, from the repository's own kernel
computation. -/
theorem complexFiniteChar_eq_one_of_mem_integral {a : RationalFiniteAdele}
    (ha : a ∈ integralFiniteAdeleSubring) : complexFiniteChar a = 1 := by
  rw [complexFiniteChar_apply, rationalFiniteAdeleFourierChar_eq_one_of_mem_integral a ha]
  exact Circle.coe_one

/-! ## Integrality of the form's values on integral vectors -/

variable {n : ℕ}

theorem coordCoe_mem_integral (x : Fin n → IntegralFiniteAdele) (i : Fin n) :
    coordCoe x i ∈ integralFiniteAdeleSubring := (x i).property

/-- The form's value is integral on integral vectors when the matrix is integral: a finite sum of
products. -/
theorem adelicQuadratic_mem_integral {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele) :
    adelicQuadratic C x ∈ integralFiniteAdeleSubring := by
  refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (coordCoe_mem_integral x i) ?_
  exact Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hC i j) (coordCoe_mem_integral x j)

/-- And SO is the polarization. -/
theorem adelicPolar_mem_integral {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) (x h : Fin n → IntegralFiniteAdele) :
    adelicPolar C x h ∈ integralFiniteAdeleSubring := by
  refine Subring.add_mem _ ?_ ?_
  · refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (coordCoe_mem_integral x i) ?_
    exact Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hC i j) (coordCoe_mem_integral h j)
  · refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (coordCoe_mem_integral h i) ?_
    exact Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hC i j) (coordCoe_mem_integral x j)

/-! ## The frequency phase and its polarization -/

/-- The frequency-scaled form. -/
noncomputable def scaledQuadratic (t : RationalFiniteAdele)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) (x : Fin n → IntegralFiniteAdele) :
    RationalFiniteAdele := t * adelicQuadratic C x

/-- And its polarization, the frequency riding through. -/
noncomputable def scaledPolar (t : RationalFiniteAdele)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) (x h : Fin n → IntegralFiniteAdele) :
    RationalFiniteAdele := t * adelicPolar C x h

theorem scaledQuadratic_polarization (t : RationalFiniteAdele)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) (x h : Fin n → IntegralFiniteAdele) :
    scaledQuadratic t C (x + h) =
      scaledQuadratic t C x + scaledPolar t C x h + scaledQuadratic t C h := by
  simp only [scaledQuadratic, scaledPolar, adelicQuadratic_polarization]
  ring

/-! ## The conductor -/

/-- The conductor condition, and it is the only input: with the matrix integral and `t * m`
integral, the character kills the level-`m` discrepancy.  The discrepancy is `(t * m)` times
something integral, so integrality of `t * m` is exactly what is needed. -/
theorem level_of_conductor (m : ℕ) {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∀ x : Fin n → IntegralFiniteAdele, ∀ h ∈ levelSubgroup n m,
      complexFiniteChar (scaledPolar t C x h + scaledQuadratic t C h) = 1 := by
  intro x h hh
  obtain ⟨u, rfl⟩ := exists_nsmul_of_mem_levelSubgroup n m h hh
  have hcoord : coordCoe (m • u) = (m : RationalFiniteAdele) • coordCoe u := by
    funext i
    change ((m • u) i : RationalFiniteAdele) = (m : RationalFiniteAdele) • coordCoe u i
    rw [show ((m • u) i : RationalFiniteAdele) = m • (u i : RationalFiniteAdele) from rfl]
    simp only [nsmul_eq_mul, smul_eq_mul]
    rfl
  have hP : adelicPolar C x (m • u) = (m : RationalFiniteAdele) * adelicPolar C x u := by
    simp only [adelicPolar, dotPolar, hcoord, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring
  have hQ : adelicQuadratic C (m • u) =
      (m : RationalFiniteAdele) * ((m : RationalFiniteAdele) * adelicQuadratic C u) := by
    simp only [adelicQuadratic, dotQuadratic, hcoord, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
  have hfactor : scaledPolar t C x (m • u) + scaledQuadratic t C (m • u) =
      (t * (m : RationalFiniteAdele)) *
        (adelicPolar C x u + (m : RationalFiniteAdele) * adelicQuadratic C u) := by
    simp only [scaledPolar, scaledQuadratic, hP, hQ]
    ring
  rw [hfactor]
  refine complexFiniteChar_eq_one_of_mem_integral (Subring.mul_mem _ htm ?_)
  exact Subring.add_mem _ (adelicPolar_mem_integral hC x u)
    (Subring.mul_mem _ (natCast_mem _ m) (adelicQuadratic_mem_integral hC u))

/-! ## The payoff, with no hypothesis on the character -/

/-- The local integral of the frequency phase over the integral finite-adelic vectors is `m ^ (-n)`
times the finite sum, for the repository's own character, with the conductor condition `t * m`
integral as the only input. -/
theorem integral_scaledPhase_eq_normalized_sum (m : ℕ) [NeZero m]
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∫ x, complexFiniteChar (scaledQuadratic t C x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ((m ^ n : ℝ))⁻¹ • ∑ q : (Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m,
        phaseQuotient (scaledQuadratic_polarization t C) complexFiniteChar
          (level_of_conductor m hC htm) q := by
  have hfib := measurableSet_preimage_mk_levelSubgroup n m (NeZero.ne m)
  rw [SMSFormula.QuadraticPhaseDescent.integral_phase_eq_average
    (integralFiniteAdeleCoordinateAddHaarMeasure n) (scaledQuadratic_polarization t C)
    complexFiniteChar (level_of_conductor m hC htm) hfib,
    card_quotient_levelSubgroup n m]
  norm_cast

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
