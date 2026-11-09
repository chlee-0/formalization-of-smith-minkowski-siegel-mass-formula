import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitValued
import SMSFormula.RationalCliffordSpinCandidatePlacewiseSpinorNormContinuity
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicRestrictedFamilyCarrier
import SMSFormula.RationalCliffordIteratedReflectionPairLift

/-!
# Rational diagonal compatibility of the adelic spinor norm

This module identifies the real and p-adic components of the specialized
full-adelic spinor norm on a rational diagonal point with the usual scalar
extensions of its rational square class.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The rational special-orthogonal diagonal embedding into the full adeles
is injective. -/
theorem rationalSpecialOrthogonalFullAdelicDiagonalHom_injective :
    Function.Injective V.rationalSpecialOrthogonalFullAdelicDiagonalHom := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hij := congrArg
    (fun z : V.FullAdelicSpecialOrthogonalGroup => z.1.1.1 i j) hgh
  change algebraMap ℚ RationalAdele (g.1.1.1 i j) =
    algebraMap ℚ RationalAdele (h.1.1.1 i j) at hij
  exact (NumberField.AdeleRing.algebraMap_injective ℤ ℚ) hij

local instance adelicSpinorNormDiagonalPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The existing rational full-adelic diagonal is the ordinary scalar-
extension map on the special-orthogonal matrix group. -/
theorem rationalSpecialOrthogonalFullAdelicDiagonalHom_eq_map
    (g : V.RationalSpecialOrthogonalGroup) :
    V.rationalSpecialOrthogonalFullAdelicDiagonalHom g =
      V.specialOrthogonalMatrixGroupMap
        (Algebra.ofId ℚ RationalAdele) g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

/-- The real component of a rational full-adelic diagonal point is its direct
real scalar extension. -/
theorem fullAdelicSpecialOrthogonalRealFinite_apply_rationalDiagonal_real
    (g : V.RationalSpecialOrthogonalGroup) :
    (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (V.rationalSpecialOrthogonalFullAdelicDiagonalHom g)).1 =
      V.specialOrthogonalMatrixGroupMap (Algebra.ofId ℚ ℝ) g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  change
    rationalInfiniteAdeleRingEquivReal
        ((algebraMap ℚ RationalAdele (g.1.1.1 i j)).1) =
      algebraMap ℚ ℝ (g.1.1.1 i j)
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
          (algebraMap ℚ RationalAdele)))
      (algebraMap ℚ ℝ))
    (g.1.1.1 i j)

/-- The finite component of a rational full-adelic diagonal point is its
direct finite-adelic scalar extension. -/
theorem fullAdelicSpecialOrthogonalRealFinite_apply_rationalDiagonal_finite
    (g : V.RationalSpecialOrthogonalGroup) :
    (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (V.rationalSpecialOrthogonalFullAdelicDiagonalHom g)).2 =
      V.specialOrthogonalMatrixGroupMap
        (Algebra.ofId ℚ RationalFiniteAdele) g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

/-- A height-one component of the finite part of a rational diagonal point is
the direct p-adic scalar extension. -/
theorem finiteAdelicSpecialOrthogonalHeightOneComponent_rationalDiagonal
    (g : V.RationalSpecialOrthogonalGroup)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v
        (V.specialOrthogonalMatrixGroupMap
          (Algebra.ofId ℚ RationalFiniteAdele) g) =
      V.specialOrthogonalMatrixGroupMap
        (Algebra.ofId ℚ
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let phi : RationalFiniteAdele →+*
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    e.toRingEquiv.toRingHom.comp ev
  change
    phi (algebraMap ℚ RationalFiniteAdele (g.1.1.1 i j)) =
      algebraMap ℚ
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (g.1.1.1 i j)
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (phi.comp (algebraMap ℚ RationalFiniteAdele))
      (algebraMap ℚ
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
    (g.1.1.1 i j)

end RationalQuadraticSpaceMatrix
