import SMSFormula.RationalAdeleAdditiveMeasure
import Mathlib.Analysis.Complex.Circle

/-!
# The archimedean additive character on the rational adeles

This file fixes the archimedean sign convention needed before constructing the
global rational-adelic Fourier character.  The character is Mathlib's
analyst-normalized real character

`x ↦ exp(2 * π * x * I)`

transported through the existing identification of the rational infinite
adele with `ℝ`.  Its pullback to the full adele ring deliberately ignores the
finite component.

The final theorem records the proof-critical obstruction: this archimedean
character is not trivial on the rational diagonal (already at `1 / 2`).  A
finite-adelic correction is therefore mandatory before any global Fourier
transform or self-dual-Haar assertion can be made.
-/

noncomputable section

open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

/-- Mathlib's positive-sign real Fourier character transported to the unique
rational infinite completion. -/
noncomputable def rationalInfiniteAdeleFourierChar :
    AddChar RationalInfiniteAdele Circle :=
  Real.fourierChar.compAddMonoidHom
    rationalInfiniteAdeleContinuousAddEquivReal.toAddEquiv.toAddMonoidHom

@[simp]
theorem rationalInfiniteAdeleFourierChar_apply
    (x : RationalInfiniteAdele) :
    rationalInfiniteAdeleFourierChar x =
      Real.fourierChar (rationalInfiniteAdeleContinuousAddEquivReal x) :=
  rfl

/-- The transported infinite-adelic character is continuous. -/
theorem continuous_rationalInfiniteAdeleFourierChar :
    Continuous rationalInfiniteAdeleFourierChar :=
  Real.continuous_fourierChar.comp
    rationalInfiniteAdeleContinuousAddEquivReal.continuous

/-- The fixed infinite-adelic real coordinate sends a rational scalar to its
usual real value. -/
@[simp]
theorem rationalInfiniteAdeleContinuousAddEquivReal_algebraMap (q : ℚ) :
    rationalInfiniteAdeleContinuousAddEquivReal
        (algebraMap ℚ RationalInfiniteAdele q) =
      algebraMap ℚ ℝ q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (algebraMap ℚ RationalInfiniteAdele))
      (algebraMap ℚ ℝ)) q

/-- On a rational scalar, the transported infinite-adelic character is the
positive-sign real Fourier character. -/
@[simp]
theorem rationalInfiniteAdeleFourierChar_algebraMap (q : ℚ) :
    rationalInfiniteAdeleFourierChar
        (algebraMap ℚ RationalInfiniteAdele q) =
      Real.fourierChar (q : ℝ) := by
  rw [rationalInfiniteAdeleFourierChar_apply,
    rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
  have hcast : (algebraMap ℚ ℝ) q = (q : ℝ) :=
    map_ratCast (algebraMap ℚ ℝ) q
  rw [hcast]

/-- The archimedean phase on the full rational adeles.  This is not the global
adelic character: the finite coordinate is intentionally ignored. -/
noncomputable def rationalAdeleArchimedeanFourierChar :
    AddChar RationalAdele Circle where
  toFun x := rationalInfiniteAdeleFourierChar x.1
  map_zero_eq_one' := AddChar.map_zero_eq_one _
  map_add_eq_mul' x y := AddChar.map_add_eq_mul _ x.1 y.1

@[simp]
theorem rationalAdeleArchimedeanFourierChar_apply (x : RationalAdele) :
    rationalAdeleArchimedeanFourierChar x =
      Real.fourierChar
        (rationalInfiniteAdeleContinuousAddEquivReal x.1) :=
  rfl

/-- The archimedean phase on the full adeles is continuous. -/
theorem continuous_rationalAdeleArchimedeanFourierChar :
    Continuous rationalAdeleArchimedeanFourierChar :=
  continuous_rationalInfiniteAdeleFourierChar.comp continuous_fst

private theorem rationalAdele_algebraMap_fst (q : ℚ) :
    (algebraMap ℚ RationalAdele q).1 =
      algebraMap ℚ RationalInfiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q

/-- The full archimedean phase has the same positive-sign formula on the
rational diagonal. -/
@[simp]
theorem rationalAdeleArchimedeanFourierChar_algebraMap (q : ℚ) :
    rationalAdeleArchimedeanFourierChar (algebraMap ℚ RationalAdele q) =
      Real.fourierChar (q : ℝ) := by
  rw [rationalAdeleArchimedeanFourierChar_apply,
    rationalAdele_algebraMap_fst,
    rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
  have hcast : (algebraMap ℚ ℝ) q = (q : ℝ) :=
    map_ratCast (algebraMap ℚ ℝ) q
  rw [hcast]

/-- The archimedean phase is trivial on diagonal integers. -/
@[simp]
theorem rationalAdeleArchimedeanFourierChar_algebraMap_intCast (z : ℤ) :
    rationalAdeleArchimedeanFourierChar
        (algebraMap ℚ RationalAdele (z : ℚ)) = 1 := by
  rw [rationalAdeleArchimedeanFourierChar_algebraMap]
  change Circle.exp (2 * Real.pi * (z : ℝ)) = 1
  exact Circle.exp_two_pi_mul_int z

/-- The archimedean phase alone is not trivial on the rational diagonal.
Thus it cannot be used as the global rational-adelic Fourier character. -/
theorem rationalAdeleArchimedeanFourierChar_algebraMap_one_div_two_ne_one :
    rationalAdeleArchimedeanFourierChar
        (algebraMap ℚ RationalAdele (1 / 2 : ℚ)) ≠ 1 := by
  rw [rationalAdeleArchimedeanFourierChar_algebraMap]
  change Circle.exp (2 * Real.pi * ((1 / 2 : ℚ) : ℝ)) ≠ 1
  have harg : 2 * Real.pi * ((1 / 2 : ℚ) : ℝ) = Real.pi := by
    norm_num
    ring
  rw [harg]
  exact Circle.exp_pi_ne_one

end PositiveDefiniteIntegralLattice
