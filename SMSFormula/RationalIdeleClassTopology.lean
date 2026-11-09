import SMSFormula.RationalIdeleClassModule
import SMSFormula.RationalAdeleAdditiveMeasure
import SMSFormula.CoveringMapBorel
import SMSFormula.RationalCliffordGeneralSpinAdelicDiagonalTopology
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicLocalCompactness
import Mathlib.Topology.Covering.Quotient

/-!
# Topology of rational idele classes

The rational-unit diagonal in the literal rational idele group is discrete
and closed.  The proof uses the standard adelic zero-neighborhood that meets
the rational diagonal only at zero.  Consequently the rational idele-class
quotient is locally compact, so its Haar measure can be used in the crossed
`GSpin` integral without introducing another adelic carrier.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Set

namespace RationalQuadraticSpaceMatrix

/-- Rational ideles use the Borel measurable structure of their intrinsic
unit-group topology. -/
noncomputable instance (priority := 2000) rationalIdeleMeasurableSpace :
    MeasurableSpace RationalAdeleˣ :=
  borel RationalAdeleˣ

noncomputable instance rationalIdeleBorelSpace : BorelSpace RationalAdeleˣ :=
  ⟨rfl⟩

/-- Rational idele classes initially use the measurable quotient of the
literal idele group by the rational diagonal.  The covering argument below
identifies this structure with Borel. -/
noncomputable instance (priority := 2000) rationalIdeleClassGroupMeasurableSpace :
    MeasurableSpace RationalIdeleClassGroup :=
  QuotientGroup.measurableSpace rationalIdeleDiagonalSubgroup

/-- The literal quotient map from rational ideles to rational idele classes. -/
def rationalIdeleClassQuotientMap : RationalAdeleˣ → RationalIdeleClassGroup :=
  QuotientGroup.mk' rationalIdeleDiagonalSubgroup

/-- An open identity neighborhood in the idele group whose rational
diagonal points consist only of one. -/
def rationalIdeleRationalDiagonalIdentityNeighborhood : Set RationalAdeleˣ :=
  {a | (a : RationalAdele) - 1 ∈ rationalAdeleDiagonalZeroNeighborhood}

theorem isOpen_rationalIdeleRationalDiagonalIdentityNeighborhood :
    IsOpen rationalIdeleRationalDiagonalIdentityNeighborhood := by
  exact isOpen_rationalAdeleDiagonalZeroNeighborhood.preimage
    (Units.continuous_val.sub continuous_const)

theorem rationalUnitFullAdelicDiagonalHom_mem_identityNeighborhood_iff
    (q : ℚˣ) :
    rationalUnitFullAdelicDiagonalHom q ∈
        rationalIdeleRationalDiagonalIdentityNeighborhood ↔ q = 1 := by
  change algebraMap ℚ RationalAdele (q : ℚ) - 1 ∈
      rationalAdeleDiagonalZeroNeighborhood ↔ q = 1
  rw [← map_one (algebraMap ℚ RationalAdele), ← map_sub,
    algebraMap_mem_rationalAdeleDiagonalZeroNeighborhood_iff]
  constructor
  · intro h
    apply Units.ext
    exact sub_eq_zero.mp h
  · rintro rfl
    simp

noncomputable instance rationalIdeleDiagonalSubgroupDiscreteTopology :
    DiscreteTopology rationalIdeleDiagonalSubgroup := by
  apply discreteTopology_of_isOpen_singleton_one
  have hopen := isOpen_rationalIdeleRationalDiagonalIdentityNeighborhood
  have hpre := hopen.preimage
    (continuous_subtype_val : Continuous
      (fun a : rationalIdeleDiagonalSubgroup => (a : RationalAdeleˣ)))
  rw [show
      (fun a : rationalIdeleDiagonalSubgroup => (a : RationalAdeleˣ)) ⁻¹'
          rationalIdeleRationalDiagonalIdentityNeighborhood =
        ({1} : Set rationalIdeleDiagonalSubgroup) by
    ext a
    constructor
    · intro ha
      rcases a.2 with ⟨q, hq⟩
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← hq,
        (rationalUnitFullAdelicDiagonalHom_mem_identityNeighborhood_iff q).mp
          (by rw [hq]; exact ha), map_one]
      rfl
    · intro ha
      have haone : a = 1 := Set.mem_singleton_iff.mp ha
      subst a
      change (1 : RationalAdeleˣ) ∈
        rationalIdeleRationalDiagonalIdentityNeighborhood
      rw [← rationalUnitFullAdelicDiagonalHom.map_one]
      exact
        (rationalUnitFullAdelicDiagonalHom_mem_identityNeighborhood_iff 1).mpr rfl]
      at hpre
  exact hpre

/-- The quotient by the discrete rational diagonal is a covering map. -/
theorem rationalIdeleClassQuotientMap_isCoveringMap :
    IsCoveringMap rationalIdeleClassQuotientMap := by
  letI : MulAction RationalAdeleˣ RationalAdeleˣ :=
    Monoid.toMulAction RationalAdeleˣ
  letI : MulAction rationalIdeleDiagonalSubgroup RationalAdeleˣ :=
    Subgroup.instMulAction
  unfold rationalIdeleClassQuotientMap
  exact
    (rationalIdeleDiagonalSubgroup.isQuotientCoveringMap_of_comm
      (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap

theorem isClosed_rationalIdeleDiagonalSubgroup :
    IsClosed (rationalIdeleDiagonalSubgroup : Set RationalAdeleˣ) := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  exact Subgroup.isClosed_of_discrete

/-- The closed rational diagonal makes the idele-class quotient Hausdorff
(indeed regular). -/
noncomputable instance rationalIdeleClassGroupT3Space :
    T3Space RationalIdeleClassGroup := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : IsClosed (rationalIdeleDiagonalSubgroup : Set RationalAdeleˣ) :=
    isClosed_rationalIdeleDiagonalSubgroup
  infer_instance

/-- Rational idele classes carry the genuine locally compact quotient
topology inherited from the existing idele group. -/
noncomputable instance rationalIdeleClassGroupLocallyCompactSpace :
    LocallyCompactSpace RationalIdeleClassGroup := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  let hUnits : LocallyCompactSpace RationalAdeleˣ := inferInstance
  letI := hUnits
  exact QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

/-- The rational idele-class quotient is second countable. -/
noncomputable instance rationalIdeleClassGroupSecondCountableTopology :
    SecondCountableTopology RationalIdeleClassGroup := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : SecondCountableTopology RationalAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (RationalAdele × RationalAdeleᵐᵒᵖ) :=
    inferInstance
  let hUnits : SecondCountableTopology RationalAdeleˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI := hUnits
  infer_instance

/-- The quotient-generated idele-class measurable structure is exactly the
Borel structure of its locally compact quotient topology. -/
theorem rationalIdeleClassGroup_measurableSpace_eq_borel :
    rationalIdeleClassGroupMeasurableSpace =
      borel RationalIdeleClassGroup := by
  letI : SecondCountableTopology RationalAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology RationalAdeleˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  unfold rationalIdeleClassGroupMeasurableSpace QuotientGroup.measurableSpace
    Quotient.instMeasurableSpace
  change MeasurableSpace.map
      (@QuotientGroup.mk RationalAdeleˣ _ rationalIdeleDiagonalSubgroup)
        (borel RationalAdeleˣ) =
    borel RationalIdeleClassGroup
  simpa [rationalIdeleClassQuotientMap, QuotientGroup.coe_mk'] using
    (MeasurableSpace.map_borel_eq_borel_of_covering
      rationalIdeleClassQuotientMap_isCoveringMap
      (QuotientGroup.mk'_surjective rationalIdeleDiagonalSubgroup))

noncomputable instance rationalIdeleClassGroupBorelSpace :
    BorelSpace RationalIdeleClassGroup :=
  ⟨rationalIdeleClassGroup_measurableSpace_eq_borel⟩

end RationalQuadraticSpaceMatrix
