import SMSFormula.RationalCliffordGeneralSpinAdelicCarrier
import SMSFormula.RationalCliffordGeneralSpinPointTopology

/-!
# Topology on the intrinsic general-Spin adelic carriers

This file specializes the finite-coordinate intrinsic `GSpin` topology to
the real, p-adic, finite-adelic, and full-adelic coefficient rings.  It
records continuity of the two crossed-diagram arrows and of the central
scalar inclusion.  The rational diagonal is treated separately: its adelic
image is handled by the same discrete-subgroup argument as the Spin and `SO`
quotients.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

theorem continuous_realCliffordGeneralSpinSimilitudeHom :
    Continuous V.realCliffordGeneralSpinSimilitudeHom :=
  V.continuous_cliffordGeneralSpinSimilitudeGroupHom ℝ

theorem continuous_padicCliffordGeneralSpinSimilitudeHom
    (p : ℕ) [Fact p.Prime] :
    Continuous (V.padicCliffordGeneralSpinSimilitudeHom p) :=
  V.continuous_cliffordGeneralSpinSimilitudeGroupHom ℚ_[p]

theorem continuous_finiteAdelicCliffordGeneralSpinSimilitudeHom :
    Continuous V.finiteAdelicCliffordGeneralSpinSimilitudeHom :=
  V.continuous_cliffordGeneralSpinSimilitudeGroupHom RationalFiniteAdele

theorem continuous_fullAdelicCliffordGeneralSpinSimilitudeHom :
    Continuous V.fullAdelicCliffordGeneralSpinSimilitudeHom :=
  V.continuous_cliffordGeneralSpinSimilitudeGroupHom RationalAdele

theorem continuous_realCliffordGeneralSpinToSpecialOrthogonalHom :
    Continuous V.realCliffordGeneralSpinToSpecialOrthogonalHom :=
  V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℝ

theorem continuous_padicCliffordGeneralSpinToSpecialOrthogonalHom
    (p : ℕ) [Fact p.Prime] :
    Continuous (V.padicCliffordGeneralSpinToSpecialOrthogonalHom p) :=
  V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℚ_[p]

theorem continuous_finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom :
    Continuous V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom :=
  V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom
    RationalFiniteAdele

theorem continuous_fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom :
    Continuous V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom :=
  V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom RationalAdele

theorem continuous_realCliffordGeneralSpinScalarGroupHom :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ) :=
  V.continuous_cliffordGeneralSpinScalarGroupHom ℝ

theorem continuous_padicCliffordGeneralSpinScalarGroupHom
    (p : ℕ) [Fact p.Prime] :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p]) :=
  V.continuous_cliffordGeneralSpinScalarGroupHom ℚ_[p]

theorem continuous_finiteAdelicCliffordGeneralSpinScalarGroupHom :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalFiniteAdele) :=
  V.continuous_cliffordGeneralSpinScalarGroupHom RationalFiniteAdele

theorem continuous_fullAdelicCliffordGeneralSpinScalarGroupHom :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele) :=
  V.continuous_cliffordGeneralSpinScalarGroupHom RationalAdele

end RationalQuadraticSpaceMatrix
