import SMSFormula.RationalAdeleAdditiveSelfDualHaar

noncomputable section

open IsDedekindDomain

namespace PositiveDefiniteIntegralLattice

theorem rationalFiniteAdele_eq_zero_of_fourierChar_mul_eq_one
    (value : RationalFiniteAdele)
    (hvalue : ∀ frequency : RationalFiniteAdele,
      rationalFiniteAdeleFourierChar (frequency * value) = 1) : value = 0 := by
  classical
  ext place
  by_contra hne
  change value place ≠ 0 at hne
  obtain ⟨outside, houtside⟩ := place.valuedAdicCompletion_surjective ℚ
    (WithZero.exp (1 : ℤ))
  let frequency : RationalFiniteAdele := RestrictedProduct.single
    (fun place : HeightOneSpectrum ℤ => place.adicCompletionIntegers ℚ)
    place (outside / value place)
  have hint := (rationalFiniteAdeleFourierChar_eq_one_iff _).mp (hvalue frequency)
  have hlocal := hint place
  change (frequency place * value place) ∈ place.adicCompletionIntegers ℚ at hlocal
  have hcoord : frequency place * value place = outside := by
    change Pi.single place (outside / value place) place * value place = outside
    rw [Pi.single_eq_same, div_mul_cancel₀ _ hne]
  rw [hcoord, HeightOneSpectrum.mem_adicCompletionIntegers, houtside] at hlocal
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hlocal
  norm_num at hlocal

theorem rationalAdele_eq_zero_of_fourierChar_mul_eq_one
    (value : RationalAdele)
    (hvalue : ∀ frequency : RationalAdele,
      rationalAdeleFourierChar (frequency * value) = 1) : value = 0 := by
  have hfinite : value.2 = 0 := by
    apply rationalFiniteAdele_eq_zero_of_fourierChar_mul_eq_one
    intro frequency
    have hphase := hvalue (0, frequency)
    change rationalAdeleFourierChar (0 * value.1, frequency * value.2) = 1 at hphase
    rw [zero_mul, rationalAdeleFourierChar_apply,
      rationalAdeleArchimedeanFourierChar_apply] at hphase
    simpa only [map_zero, AddChar.map_zero_eq_one, one_mul] using hphase
  have hinfinite : value.1 = 0 := by
    apply rationalInfiniteAdeleRingEquivReal.injective
    rw [map_zero]
    by_contra hne
    let frequency : RationalAdele :=
      (rationalInfiniteAdeleRingEquivReal.symm
        (1 / (2 * rationalInfiniteAdeleRingEquivReal value.1)), 0)
    have hreal : rationalInfiniteAdeleContinuousAddEquivReal
        (frequency * value).1 = (1 / 2 : ℝ) := by
      change rationalInfiniteAdeleRingEquivReal
        (rationalInfiniteAdeleRingEquivReal.symm
          (1 / (2 * rationalInfiniteAdeleRingEquivReal value.1)) * value.1) = _
      rw [map_mul, RingEquiv.apply_symm_apply]
      field_simp
    have hphase := hvalue frequency
    rw [rationalAdeleFourierChar_apply, rationalAdeleArchimedeanFourierChar_apply,
      hreal] at hphase
    have hzero : (frequency * value).2 = 0 := zero_mul _
    rw [hzero, AddChar.map_zero_eq_one, mul_one] at hphase
    change Circle.exp (2 * Real.pi * (1 / 2 : ℝ)) = 1 at hphase
    have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
    exact Circle.exp_pi_ne_one (harg ▸ hphase)
  exact Prod.ext hinfinite hfinite

theorem rationalAdele_eq_of_fourierChar_mul_eq
    {left right : RationalAdele}
    (heq : ∀ frequency : RationalAdele,
      rationalAdeleFourierChar (frequency * left) =
        rationalAdeleFourierChar (frequency * right)) : left = right := by
  apply sub_eq_zero.mp
  apply rationalAdele_eq_zero_of_fourierChar_mul_eq_one
  intro frequency
  rw [mul_sub, AddChar.map_sub_eq_div, heq, div_self']

theorem rationalAdele_fourierChar_separatesPoints
    {left right : RationalAdele} (hne : left ≠ right) :
    ∃ frequency : RationalAdele,
      rationalAdeleFourierChar (frequency * left) ≠
        rationalAdeleFourierChar (frequency * right) := by
  contrapose! hne
  exact rationalAdele_eq_of_fourierChar_mul_eq hne

end PositiveDefiniteIntegralLattice
