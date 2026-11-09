import SMSFormula.RationalAdeleAdditiveQuotient
import SMSFormula.RationalFiniteAdeleAdditiveCharacter

/-!
# Characters and orthogonality on the additive adelic quotient

The fixed global rational-adelic character is trivial on the rational
diagonal.  This file scales it by a rational frequency, descends it to the
literal compact quotient `𝔸_ℚ / ℚ`, and proves the exact probability-Haar
orthogonality relation.

The zero-frequency integral is the total probability mass.  At nonzero
frequency, an explicit purely archimedean adele has phase `exp(π i)`, and
translation invariance forces the character integral to vanish.  No
Pontryagin-duality or generic character-classification theorem is used.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PositiveDefiniteIntegralLattice

/-- Multiplication by a rational diagonal scalar as an additive homomorphism
of the full rational adeles. -/
def rationalAdeleRationalScalarAddMonoidHom (t : ℚ) :
    RationalAdele →+ RationalAdele where
  toFun a := algebraMap ℚ RationalAdele t * a
  map_zero' := by simp
  map_add' a b := by rw [mul_add]

/-- The fixed global additive character at rational frequency `t`. -/
noncomputable def rationalAdeleScaledFourierChar (t : ℚ) :
    AddChar RationalAdele Circle :=
  rationalAdeleFourierChar.compAddMonoidHom
    (rationalAdeleRationalScalarAddMonoidHom t)

@[simp]
theorem rationalAdeleScaledFourierChar_apply (t : ℚ) (a : RationalAdele) :
    rationalAdeleScaledFourierChar t a =
      rationalAdeleFourierChar (algebraMap ℚ RationalAdele t * a) :=
  rfl

theorem continuous_rationalAdeleScaledFourierChar (t : ℚ) :
    Continuous (rationalAdeleScaledFourierChar t) :=
  continuous_rationalAdeleFourierChar.comp
    (continuous_const.mul continuous_id)

/-- Every rational-frequency character is trivial on the rational diagonal. -/
theorem rationalAdeleScaledFourierChar_eq_one_of_mem_diagonal
    (t : ℚ) (a : RationalAdele)
    (ha : a ∈ rationalAdeleRationalDiagonalAddSubgroup) :
    rationalAdeleScaledFourierChar t a = 1 := by
  rcases ha with ⟨q, rfl⟩
  rw [rationalAdeleScaledFourierChar_apply, ← map_mul]
  exact rationalAdeleFourierChar_algebraMap (t * q)

/-- The rational-frequency global character descended algebraically to
`𝔸_ℚ / ℚ`. -/
noncomputable def rationalAdeleModRationalFourierChar (t : ℚ) :
    AddChar RationalAdeleModRational Circle :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift rationalAdeleRationalDiagonalAddSubgroup
      (rationalAdeleScaledFourierChar t).toAddMonoidHom (by
        intro a ha
        exact congrArg Additive.ofMul
          (rationalAdeleScaledFourierChar_eq_one_of_mem_diagonal t a ha)))

@[simp]
theorem rationalAdeleModRationalFourierChar_mk
    (t : ℚ) (a : RationalAdele) :
    rationalAdeleModRationalFourierChar t
        (rationalAdeleModRationalQuotientMap a) =
      rationalAdeleScaledFourierChar t a :=
  rfl

/-- The descended quotient character is continuous in the existing quotient
topology. -/
theorem continuous_rationalAdeleModRationalFourierChar (t : ℚ) :
    Continuous (rationalAdeleModRationalFourierChar t) := by
  rw [(QuotientAddGroup.isQuotientMap_mk
    rationalAdeleRationalDiagonalAddSubgroup).continuous_iff]
  exact continuous_rationalAdeleScaledFourierChar t

private theorem rationalAdele_algebraMap_fst_quotientCharacter (q : ℚ) :
    (algebraMap ℚ RationalAdele q).1 =
      algebraMap ℚ RationalInfiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q

/-- A purely archimedean adele on which frequency `t ≠ 0` has phase `1/2`
modulo `1`. -/
noncomputable def rationalAdeleHalfFrequencyWitness (t : ℚ) : RationalAdele :=
  (rationalInfiniteAdeleContinuousAddEquivReal.symm
      (1 / (2 * (t : ℝ))), 0)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit half-frequency witness has nontrivial global phase at every
nonzero rational frequency. -/
theorem rationalAdeleScaledFourierChar_halfFrequencyWitness_ne_one
    (t : ℚ) (ht : t ≠ 0) :
    rationalAdeleScaledFourierChar t
        (rationalAdeleHalfFrequencyWitness t) ≠ 1 := by
  rw [rationalAdeleScaledFourierChar_apply,
    rationalAdeleFourierChar_apply,
    rationalAdeleArchimedeanFourierChar_apply]
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hinf :
      rationalInfiniteAdeleContinuousAddEquivReal
          ((algebraMap ℚ RationalAdele t *
            rationalAdeleHalfFrequencyWitness t).1) = (1 / 2 : ℝ) := by
    rw [Prod.fst_mul, rationalAdele_algebraMap_fst_quotientCharacter]
    change rationalInfiniteAdeleRingEquivReal
        (algebraMap ℚ RationalInfiniteAdele t *
          rationalInfiniteAdeleContinuousAddEquivReal.symm
            (1 / (2 * (t : ℝ)))) = _
    rw [map_mul]
    have htmap :
        rationalInfiniteAdeleRingEquivReal
            (algebraMap ℚ RationalInfiniteAdele t) = (t : ℝ) := by
      exact rationalInfiniteAdeleContinuousAddEquivReal_algebraMap t
    have hsymm :
        rationalInfiniteAdeleRingEquivReal
            (rationalInfiniteAdeleContinuousAddEquivReal.symm
              (1 / (2 * (t : ℝ)))) = 1 / (2 * (t : ℝ)) := by
      change rationalInfiniteAdeleContinuousAddEquivReal
          (rationalInfiniteAdeleContinuousAddEquivReal.symm
            (1 / (2 * (t : ℝ)))) = _
      exact rationalInfiniteAdeleContinuousAddEquivReal.apply_symm_apply _
    rw [htmap, hsymm]
    field_simp
  rw [hinf]
  have hsnd :
      ((algebraMap ℚ RationalAdele t *
        rationalAdeleHalfFrequencyWitness t).2) = 0 := by
    change (algebraMap ℚ RationalAdele t).2 *
      (0 : RationalFiniteAdele) = 0
    exact mul_zero _
  rw [hsnd, AddChar.map_zero_eq_one, mul_one]
  change Circle.exp (2 * Real.pi * (1 / 2 : ℝ)) ≠ 1
  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [harg]
  exact Circle.exp_pi_ne_one

/-- Every nonzero rational frequency gives a nontrivial character on the
additive adelic quotient. -/
theorem rationalAdeleModRationalFourierChar_ne_one
    (t : ℚ) (ht : t ≠ 0) :
    rationalAdeleModRationalFourierChar t ≠ 1 := by
  intro h
  have happ := DFunLike.congr_fun h
    (rationalAdeleModRationalQuotientMap
      (rationalAdeleHalfFrequencyWitness t))
  rw [rationalAdeleModRationalFourierChar_mk] at happ
  exact rationalAdeleScaledFourierChar_halfFrequencyWitness_ne_one t ht
    (by simpa using happ)

/-- Exact character orthogonality for the probability Haar on `𝔸_ℚ / ℚ`. -/
theorem integral_rationalAdeleModRationalFourierChar
    (t : ℚ) :
    ∫ a, (rationalAdeleModRationalFourierChar t a : ℂ)
        ∂rationalAdeleModRationalProbabilityHaarMeasure =
      if t = 0 then 1 else 0 := by
  by_cases ht : t = 0
  · subst t
    have hfun :
        (fun a : RationalAdeleModRational =>
          (rationalAdeleModRationalFourierChar 0 a : ℂ)) =
        fun _ => 1 := by
      funext a
      induction a using Quotient.inductionOn with
      | h x =>
          change ((rationalAdeleScaledFourierChar 0 x : Circle) : ℂ) = 1
          simp [rationalAdeleScaledFourierChar_apply]
    rw [hfun, integral_const]
    simp
  · rw [if_neg ht]
    let chi := rationalAdeleModRationalFourierChar t
    let y := rationalAdeleModRationalQuotientMap
      (rationalAdeleHalfFrequencyWitness t)
    let I : ℂ := ∫ a, (chi a : ℂ)
      ∂rationalAdeleModRationalProbabilityHaarMeasure
    have htranslate : (chi y : ℂ) * I = I := by
      calc
        (chi y : ℂ) * I =
            ∫ a, (chi y : ℂ) * (chi a : ℂ)
              ∂rationalAdeleModRationalProbabilityHaarMeasure := by
                rw [integral_const_mul]
        _ = ∫ a, (chi (y + a) : ℂ)
              ∂rationalAdeleModRationalProbabilityHaarMeasure := by
                congr 1
                funext a
                rw [AddChar.map_add_eq_mul, Circle.coe_mul]
        _ = I := integral_add_left_eq_self
          (fun a => (chi a : ℂ)) y
    have hchi : (chi y : ℂ) ≠ 1 := by
      intro h
      have hcircle : chi y = 1 := Subtype.ext h
      exact rationalAdeleScaledFourierChar_halfFrequencyWitness_ne_one t ht
        (by simpa [chi, y] using hcircle)
    have hzero : ((chi y : ℂ) - 1) * I = 0 := by
      rw [sub_mul, htranslate, one_mul, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hchi)

end PositiveDefiniteIntegralLattice
