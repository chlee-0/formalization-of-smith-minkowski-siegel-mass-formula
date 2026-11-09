import SMSFormula.RationalCliffordGeneralSpinNaturality
import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier

/-!
# Rational, local, and adelic intrinsic general-Spin carriers

This file evaluates the intrinsic general-Spin point group on the rational,
real, p-adic, finite-adelic, and full-adelic coefficient algebras.  The
diagonal maps, similitude characters, and projections to the existing `SO`
carriers are the natural scalar-extension maps.
No topology or measure is installed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

abbrev RationalCliffordGeneralSpinGroup :=
  V.CliffordGeneralSpinIntrinsicPoint ℚ

abbrev RealCliffordGeneralSpinGroup :=
  V.CliffordGeneralSpinIntrinsicPoint ℝ

abbrev PadicCliffordGeneralSpinGroup
    (p : ℕ) [Fact p.Prime] :=
  V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]

abbrev FiniteAdelicCliffordGeneralSpinGroup :=
  V.CliffordGeneralSpinIntrinsicPoint RationalFiniteAdele

abbrev FullAdelicCliffordGeneralSpinGroup :=
  V.CliffordGeneralSpinIntrinsicPoint RationalAdele

def rationalCliffordGeneralSpinRealDiagonalHom :
    V.RationalCliffordGeneralSpinGroup →*
      V.RealCliffordGeneralSpinGroup :=
  CliffordGeneralSpinIntrinsicPoint.mapGroupHom V (Algebra.ofId ℚ ℝ)

def rationalCliffordGeneralSpinPadicDiagonalHom
    (p : ℕ) [Fact p.Prime] :
    V.RationalCliffordGeneralSpinGroup →*
      V.PadicCliffordGeneralSpinGroup p :=
  CliffordGeneralSpinIntrinsicPoint.mapGroupHom V
    (Algebra.ofId ℚ ℚ_[p])

def rationalCliffordGeneralSpinFiniteAdelicDiagonalHom :
    V.RationalCliffordGeneralSpinGroup →*
      V.FiniteAdelicCliffordGeneralSpinGroup :=
  CliffordGeneralSpinIntrinsicPoint.mapGroupHom V
    (Algebra.ofId ℚ RationalFiniteAdele)

def rationalCliffordGeneralSpinFullAdelicDiagonalHom :
    V.RationalCliffordGeneralSpinGroup →*
      V.FullAdelicCliffordGeneralSpinGroup :=
  CliffordGeneralSpinIntrinsicPoint.mapGroupHom V
    (Algebra.ofId ℚ RationalAdele)

/-- The diagonal rational subgroup inside the full-adelic intrinsic
general-Spin group. -/
def rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :
    Subgroup V.FullAdelicCliffordGeneralSpinGroup :=
  V.rationalCliffordGeneralSpinFullAdelicDiagonalHom.range

/-- The carrier-specific rational left quotient of full-adelic intrinsic
general Spin. -/
abbrev FullAdelicCliffordGeneralSpinLeftQuotient :=
  leftCosetSet V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup

/-- The canonical map to the rational full-adelic intrinsic general-Spin
left quotient. -/
def fullAdelicCliffordGeneralSpinLeftQuotientMap :
    V.FullAdelicCliffordGeneralSpinGroup →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  leftCosetMap V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup

def realCliffordGeneralSpinSimilitudeHom :
    V.RealCliffordGeneralSpinGroup →* ℝˣ :=
  CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℝ

def padicCliffordGeneralSpinSimilitudeHom
    (p : ℕ) [Fact p.Prime] :
    V.PadicCliffordGeneralSpinGroup p →* ℚ_[p]ˣ :=
  CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ_[p]

def finiteAdelicCliffordGeneralSpinSimilitudeHom :
    V.FiniteAdelicCliffordGeneralSpinGroup →* RationalFiniteAdeleˣ :=
  CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V RationalFiniteAdele

def fullAdelicCliffordGeneralSpinSimilitudeHom :
    V.FullAdelicCliffordGeneralSpinGroup →* RationalAdeleˣ :=
  CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V RationalAdele

def realCliffordGeneralSpinToSpecialOrthogonalHom :
    V.RealCliffordGeneralSpinGroup →* V.RealSpecialOrthogonalGroup :=
  CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℝ

def padicCliffordGeneralSpinToSpecialOrthogonalHom
    (p : ℕ) [Fact p.Prime] :
    V.PadicCliffordGeneralSpinGroup p →*
      V.specialOrthogonalMatrixGroup ℚ_[p] :=
  CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ_[p]

def finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom :
    V.FiniteAdelicCliffordGeneralSpinGroup →*
      V.FiniteAdelicSpecialOrthogonalGroup :=
  CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V
    RationalFiniteAdele

def fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom :
    V.FullAdelicCliffordGeneralSpinGroup →*
      V.FullAdelicSpecialOrthogonalGroup :=
  CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V
    RationalAdele

@[simp]
theorem rational_real_diagonal_generalSpin_similitude
    (x : V.RationalCliffordGeneralSpinGroup) :
    V.realCliffordGeneralSpinSimilitudeHom
        (V.rationalCliffordGeneralSpinRealDiagonalHom x) =
      Units.map (algebraMap ℚ ℝ).toMonoidHom x.similitude :=
  rfl

@[simp]
theorem rational_padic_diagonal_generalSpin_similitude
    (p : ℕ) [Fact p.Prime]
    (x : V.RationalCliffordGeneralSpinGroup) :
    V.padicCliffordGeneralSpinSimilitudeHom p
        (V.rationalCliffordGeneralSpinPadicDiagonalHom p x) =
      Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom x.similitude :=
  rfl

theorem rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal
    (x : V.RationalCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom x) =
      V.specialOrthogonalMatrixGroupMap (Algebra.ofId ℚ RationalAdele)
        (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ x) := by
  exact (DFunLike.congr_fun
    (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonal_naturality V
      (Algebra.ofId ℚ RationalAdele)) x).symm

theorem rational_finiteAdelic_diagonal_generalSpinToSpecialOrthogonal
    (x : V.RationalCliffordGeneralSpinGroup) :
    V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (V.rationalCliffordGeneralSpinFiniteAdelicDiagonalHom x) =
      V.specialOrthogonalMatrixGroupMap
        (Algebra.ofId ℚ RationalFiniteAdele)
        (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ x) := by
  exact (DFunLike.congr_fun
    (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonal_naturality V
      (Algebra.ofId ℚ RationalFiniteAdele)) x).symm

end RationalQuadraticSpaceMatrix
