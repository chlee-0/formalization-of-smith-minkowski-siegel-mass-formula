import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalAction
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicLocalCompactness
import Mathlib.Topology.CompactOpen

/-!
# Topology of the horizontal idele-class action

The rational adelic general-Spin quotient map is open, hence its existing
quotient topology is locally compact.  The product of the two open quotient
maps lets the central action descend jointly and continuously through both
the general-Spin quotient and the rational idele-class quotient.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 300000

/-- The inverse image of the quotient image of a set is the union of its
rational left translates. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_preimage_image
    (U : Set V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap ⁻¹'
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap '' U) =
      ⋃ gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
        (fun x : V.FullAdelicCliffordGeneralSpinGroup =>
          (gamma : V.FullAdelicCliffordGeneralSpinGroup) * x) '' U := by
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    have hrel : IsLeftCosetRelated
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup u x :=
      (leftCoset_mk_eq_iff
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup u x).mp hux
    rcases hrel with ⟨gamma, rfl⟩
    exact Set.mem_iUnion.mpr ⟨gamma, ⟨u, hu, rfl⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨gamma, u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    exact (leftCosetMap_gamma_mul
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup gamma u).symm

/-- The rational general-Spin left quotient map is open. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenMap :
    IsOpenMap V.fullAdelicCliffordGeneralSpinLeftQuotientMap := by
  intro U hU
  rw [isOpen_coinduced,
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_preimage_image U]
  exact isOpen_iUnion fun gamma =>
    isOpenMap_mul_left
      (gamma : V.FullAdelicCliffordGeneralSpinGroup) U hU

/-- The rational general-Spin left quotient map is an open quotient map. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenQuotientMap :
    IsOpenQuotientMap V.fullAdelicCliffordGeneralSpinLeftQuotientMap :=
  IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenMap
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap

/-- The existing rational adelic general-Spin left quotient is locally
compact. -/
noncomputable instance
    fullAdelicCliffordGeneralSpinLeftQuotientLocallyCompactSpace :
    LocallyCompactSpace V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenQuotientMap
    |>.locallyCompactSpace

/-- Joint continuity of the central rational idele-class action. -/
theorem continuous_rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient :
    Continuous (fun p : RationalIdeleClassGroup ×
        V.FullAdelicCliffordGeneralSpinLeftQuotient =>
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        p.1 p.2) := by
  let Q : IsOpenQuotientMap
      (Prod.map
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup)
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap) :=
    QuotientGroup.isOpenQuotientMap_mk.prodMap
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenQuotientMap
  apply Q.isQuotientMap.continuous_iff.mpr
  have hrep : Continuous (fun p : RationalAdeleˣ ×
      V.FullAdelicCliffordGeneralSpinGroup =>
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele p.1 * p.2)) :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
      ((V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
        continuous_fst).mul continuous_snd)
  simpa [Q, Prod.map,
    rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient,
    fullAdelicCliffordGeneralSpinLeftQuotientScalarActionOfIdele]
    using hrep

end RationalQuadraticSpaceMatrix
