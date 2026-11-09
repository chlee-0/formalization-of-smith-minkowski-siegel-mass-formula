import SMSFormula.CoveringMapBorel
import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalActionTopology
import SMSFormula.RationalCliffordSpinCandidateRawGeneralSpinQuotientPushforward
import Mathlib.Topology.Covering.Quotient

/-!
# The Borel structure on the adelic general-Spin quotient

The rational general-Spin diagonal is discrete, so its left quotient map is a
covering map.  An explicit finite-coordinate second-countability argument and
`MeasurableSpace.map_borel_eq_borel_of_covering` identify the map-generated
quotient measurable structure with the Borel structure of the quotient
topology.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

/-- A witness that full-adelic intrinsic general Spin is second countable in
its finite-coordinate topology.  It is not a global instance; it is used only
in the quotient Borel comparison below. -/
noncomputable def fullAdelicCliffordGeneralSpinGroupSecondCountableTopology :
    SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup := by
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  let hCoeff : SecondCountableTopology (Finset (Fin n) → RationalAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI := hCoeff
  let hCoeffPair : SecondCountableTopology
      ((Finset (Fin n) → RationalAdele) ×
        (Finset (Fin n) → RationalAdele)) :=
    @TopologicalSpace.instSecondCountableTopologyProd _ _ _ _ hCoeff hCoeff
  letI : SecondCountableTopology RationalAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (RationalAdele × RationalAdeleᵐᵒᵖ) :=
    inferInstance
  let hUnits : SecondCountableTopology RationalAdeleˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI := hCoeffPair
  letI := hUnits
  let hCliffordUnits : SecondCountableTopology
      (((Finset (Fin n) → RationalAdele) ×
          (Finset (Fin n) → RationalAdele)) × RationalAdeleˣ) :=
    @TopologicalSpace.instSecondCountableTopologyProd _ _ _ _
      hCoeffPair hUnits
  let hSO : SecondCountableTopology V.FullAdelicSpecialOrthogonalGroup :=
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph
      |>.isEmbedding.secondCountableTopology
  let hClosed : SecondCountableTopology
      (V.CliffordGeneralSpinClosedCoordinateSpace RationalAdele) :=
    @TopologicalSpace.instSecondCountableTopologyProd _ _ _ _
      hCliffordUnits hSO
  letI := hClosed
  exact V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding RationalAdele
    |>.isEmbedding.secondCountableTopology

/-- A witness that the actual rational adelic general-Spin quotient topology
is second countable.  Like the source witness, it is deliberately local to
the Borel comparison. -/
noncomputable def
    fullAdelicCliffordGeneralSpinLeftQuotientSecondCountableTopology :
    SecondCountableTopology V.FullAdelicCliffordGeneralSpinLeftQuotient := by
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap
    |>.secondCountableTopology
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenMap

/-- The quotient by the discrete rational general-Spin diagonal is a
covering map. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_isCoveringMap :
    IsCoveringMap V.fullAdelicCliffordGeneralSpinLeftQuotientMap := by
  letI : DiscreteTopology
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroupDiscreteTopology
  let hcov : IsQuotientCoveringMap
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
    apply V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap
      |>.isQuotientCoveringMap_of_subgroup
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        DiscreteTopology.isDiscrete
    intro x y
    change Quot.mk
        (leftCosetSetoid
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) x =
      Quot.mk
        (leftCosetSetoid
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) y ↔ _
    rw [leftCoset_mk_eq_iff]
    constructor
    · rintro ⟨gamma, rfl⟩
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using gamma.2
    · intro hxy
      exact ⟨⟨y * x⁻¹, hxy⟩, by simp⟩
  exact hcov.isCoveringMap

/-- The map-generated quotient measurable structure used by the raw Spin
pushforward is literally the Borel structure of the genuine quotient
topology. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotient_measurableSpace_eq_borel :
    (inferInstance :
      MeasurableSpace V.FullAdelicCliffordGeneralSpinLeftQuotient) =
      borel V.FullAdelicCliffordGeneralSpinLeftQuotient := by
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  letI : SecondCountableTopology
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientSecondCountableTopology
  change MeasurableSpace.map
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (borel V.FullAdelicCliffordGeneralSpinGroup) =
    borel V.FullAdelicCliffordGeneralSpinLeftQuotient
  exact MeasurableSpace.map_borel_eq_borel_of_covering
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isCoveringMap
    (by
      intro z
      induction z using Quot.inductionOn with
      | _ x => exact ⟨x, rfl⟩)

noncomputable instance fullAdelicCliffordGeneralSpinLeftQuotientBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  ⟨V.fullAdelicCliffordGeneralSpinLeftQuotient_measurableSpace_eq_borel⟩

end RationalQuadraticSpaceMatrix
