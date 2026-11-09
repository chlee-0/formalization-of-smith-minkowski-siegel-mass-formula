import SMSFormula.RationalAdeleRankOneAdelicBruhatFactorization
import SMSFormula.RationalFiniteAdeleStrongApproximation

/-!
# Strong-approximation reduction of adelic finite Gauss parameters

The generalized finite quadratic Gauss integral only sees its finite-adelic
parameter modulo the integral finite adeles.  Finite strong approximation
therefore reduces any fixed parameter, and its whole rational translate
family, to the already estimated rational Gauss integrals.

The reduction is existential.  No representative-valued function or section
of the finite-adelic quotient is defined.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- An integral change of finite-adelic parameter does not change the
quadratic phase on the standard integral vector lattice. -/
theorem rationalFiniteAdeleQuadraticPhaseAt_add_integral_mul_indicator
    (L : PositiveDefiniteIntegralLattice n)
    (s z : RationalFiniteAdele)
    (hz : z ∈ integralFiniteAdeleSubring)
    (x : Fin n → RationalFiniteAdele) :
    (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt
        (s + z) x : ℂ) * rationalFiniteAdeleVectorIntegralIndicator x =
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt
        s x : ℂ) * rationalFiniteAdeleVectorIntegralIndicator x := by
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx]
    simp only [mul_one]
    unfold rationalFiniteAdeleQuadraticPhaseAt
    rw [add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
    have hq :
        L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x ∈
          integralFiniteAdeleSubring := by
      simpa [finiteAdelicQuadraticFormValue] using
        L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring x x hx hx
    have hzq : z *
        L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x ∈
          integralFiniteAdeleSubring :=
      Subring.mul_mem integralFiniteAdeleSubring hz hq
    rw [rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hzq]
    simp
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
    simp

/-- The generalized finite Gauss integral depends only on its parameter
modulo the integral finite adeles. -/
theorem rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral
    (L : PositiveDefiniteIntegralLattice n)
    (s z : RationalFiniteAdele)
    (hz : z ∈ integralFiniteAdeleSubring) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt
        (s + z) =
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt
        s := by
  unfold rationalFiniteAdeleQuadraticGaussIntegralAt
  apply integral_congr_ae
  filter_upwards
  intro x
  exact rationalFiniteAdeleQuadraticPhaseAt_add_integral_mul_indicator L
    s z hz x

/-- Any generalized finite Gauss integral equals an old rational-parameter
Gauss integral.  The rational approximant remains existential. -/
theorem exists_rational_rationalFiniteAdeleQuadraticGaussIntegralAt_eq
    (L : PositiveDefiniteIntegralLattice n) (s : RationalFiniteAdele) :
    ∃ q : ℚ,
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt
          s =
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral q := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integralFiniteAdeleSubring s
  refine ⟨q, ?_⟩
  let z := s - algebraMap ℚ RationalFiniteAdele q
  have hs : s = algebraMap ℚ RationalFiniteAdele q + z := by
    simp [z]
  rw [hs]
  exact rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral L
    (algebraMap ℚ RationalFiniteAdele q) z hq

/-- A fixed finite-adelic parameter plus every rational diagonal parameter is
simultaneously reduced by one existential rational translate. -/
theorem exists_rational_rationalFiniteAdeleQuadraticGaussIntegralAt_add_diagonal_eq
    (L : PositiveDefiniteIntegralLattice n) (s : RationalFiniteAdele) :
    ∃ q : ℚ, ∀ t : ℚ,
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt
          (s + algebraMap ℚ RationalFiniteAdele t) =
        (L.rationalQuadraticSpaceMatrix
          |>.rationalFiniteAdeleQuadraticGaussIntegral (t + q)) := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integralFiniteAdeleSubring s
  refine ⟨q, fun t ↦ ?_⟩
  let z := s - algebraMap ℚ RationalFiniteAdele q
  have hs :
      s + algebraMap ℚ RationalFiniteAdele t =
        algebraMap ℚ RationalFiniteAdele (t + q) + z := by
    simp only [map_add]
    simp [z]
    ring
  rw [hs]
  exact rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral L
    (algebraMap ℚ RationalFiniteAdele (t + q)) z hq

end RationalQuadraticSpaceMatrix

end
