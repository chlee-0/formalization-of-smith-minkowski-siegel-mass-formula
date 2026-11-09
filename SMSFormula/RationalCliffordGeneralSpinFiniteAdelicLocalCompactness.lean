import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicRestrictedFamily
import SMSFormula.RationalAdeleAdditiveMeasure
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialMeasureRegularity
import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier

/-!
# Local compactness of finite-adelic intrinsic general Spin

The finite-coordinate realization of intrinsic `GSpin` is closed.  This file
supplies its ambient product local-compactness instance explicitly, avoiding
an expensive search through the nested coordinate abbreviation.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance finiteAdelicGeneralSpinFiniteT2 : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicGeneralSpinInfiniteT2 : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicGeneralSpinAdeleT2 : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

/-- Intrinsic general Spin over the finite rational adeles is locally compact
in its existing finite-coordinate topology. -/
noncomputable instance finiteAdelicCliffordGeneralSpinGroupLocallyCompactSpace :
    LocallyCompactSpace V.FiniteAdelicCliffordGeneralSpinGroup := by
  let hCoeff : LocallyCompactSpace
      (Finset (Fin n) → RationalFiniteAdele) :=
    Pi.locallyCompactSpace_of_finite
  let hCoeffPair : LocallyCompactSpace
      ((Finset (Fin n) → RationalFiniteAdele) ×
        (Finset (Fin n) → RationalFiniteAdele)) :=
    @Prod.locallyCompactSpace _ _ _ _ hCoeff hCoeff
  let hUnits : LocallyCompactSpace RationalFiniteAdeleˣ := inferInstance
  let hCliffordUnits : LocallyCompactSpace
      (((Finset (Fin n) → RationalFiniteAdele) ×
          (Finset (Fin n) → RationalFiniteAdele)) × RationalFiniteAdeleˣ) :=
    @Prod.locallyCompactSpace _ _ _ _ hCoeffPair hUnits
  let hSO : LocallyCompactSpace V.FiniteAdelicSpecialOrthogonalGroup :=
    V.finiteAdelicSpecialOrthogonalGroupLocallyCompactSpace
  let hClosed : LocallyCompactSpace
      (V.CliffordGeneralSpinClosedCoordinateSpace RationalFiniteAdele) :=
    @Prod.locallyCompactSpace _ _ _ _ hCliffordUnits hSO
  letI := hClosed
  exact Topology.IsClosedEmbedding.locallyCompactSpace
    (Y := V.CliffordGeneralSpinClosedCoordinateSpace RationalFiniteAdele)
    (V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding
      RationalFiniteAdele)

/-- Intrinsic general Spin over the full rational adeles is locally compact
in its existing finite-coordinate topology. -/
noncomputable instance fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace :
    LocallyCompactSpace V.FullAdelicCliffordGeneralSpinGroup := by
  let hCoeff : LocallyCompactSpace (Finset (Fin n) → RationalAdele) :=
    Pi.locallyCompactSpace_of_finite
  let hCoeffPair : LocallyCompactSpace
      ((Finset (Fin n) → RationalAdele) ×
        (Finset (Fin n) → RationalAdele)) :=
    @Prod.locallyCompactSpace _ _ _ _ hCoeff hCoeff
  let hUnits : LocallyCompactSpace RationalAdeleˣ := inferInstance
  let hCliffordUnits : LocallyCompactSpace
      (((Finset (Fin n) → RationalAdele) ×
          (Finset (Fin n) → RationalAdele)) × RationalAdeleˣ) :=
    @Prod.locallyCompactSpace _ _ _ _ hCoeffPair hUnits
  let hSO : LocallyCompactSpace V.FullAdelicSpecialOrthogonalGroup :=
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph
      |>.locallyCompactSpace_iff.mpr inferInstance
  let hClosed : LocallyCompactSpace
      (V.CliffordGeneralSpinClosedCoordinateSpace RationalAdele) :=
    @Prod.locallyCompactSpace _ _ _ _ hCliffordUnits hSO
  letI := hClosed
  exact Topology.IsClosedEmbedding.locallyCompactSpace
    (Y := V.CliffordGeneralSpinClosedCoordinateSpace RationalAdele)
    (V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding RationalAdele)

end RationalQuadraticSpaceMatrix
